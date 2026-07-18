const WebSocket = require('ws');
const https = require('https');
const http = require('http');
const dgram = require('dgram');
const fs = require('fs');
const path = require('path');

// EPIPE and EOF are expected when ffmpeg or yt-dlp exits while the other process
// is still piping data (async writes in flight). They are safe to ignore; every
// code path that matters already handles the resulting idle/stop state.
process.on('uncaughtException', (err) => {
  if (err.code === 'EPIPE' || err.code === 'EOF') return;
  throw err;
});
const _logFile = path.join(require('os').tmpdir(), 'discord-rpc-voice.log');

// ── NSFW channel state persistence ──
const _nsfwStateFile = path.join(process.env.KP_DATA_DIR || __dirname, 'nsfw-state.json');
function _loadNsfwState() {
  try { return JSON.parse(fs.readFileSync(_nsfwStateFile, 'utf8')); } catch { return {}; }
}
function _saveNsfwState(channels, roles) {
  try {
    fs.writeFileSync(_nsfwStateFile, JSON.stringify({
      channels: [...channels],
      roles: [...roles.entries()],
    }), 'utf8');
  } catch {}
}
const _nsfwDedupFile = path.join(process.env.KP_DATA_DIR || __dirname, 'nsfw-dedup.json');
function _loadNsfwDedup() {
  try {
    const raw = JSON.parse(fs.readFileSync(_nsfwDedupFile, 'utf8'));
    const map = new Map();
    for (const [k, ids] of Object.entries(raw)) map.set(k, new Set(ids));
    return map;
  } catch { return new Map(); }
}
function _saveNsfwDedup(map) {
  try {
    const out = {};
    for (const [k, s] of map) out[k] = [...s].slice(-2000); // keep last 2000 per guild
    fs.writeFileSync(_nsfwDedupFile, JSON.stringify(out), 'utf8');
  } catch {}
}
// Persist subreddit rotation indexes so bot restarts don't reset back to the same first batch.
const _nsfwSubIdxFile = path.join(process.env.KP_DATA_DIR || __dirname, 'nsfw-subidx.json');
function _loadNsfwSubIdx() {
  try {
    const raw = JSON.parse(fs.readFileSync(_nsfwSubIdxFile, 'utf8'));
    const map = new Map();
    for (const [k, v] of Object.entries(raw)) map.set(k, v);
    return map;
  } catch { return new Map(); }
}
function _saveNsfwSubIdx(map) {
  try {
    const out = {};
    for (const [k, v] of map) out[k] = v;
    fs.writeFileSync(_nsfwSubIdxFile, JSON.stringify(out), 'utf8');
  } catch {}
}
function vlog(...args) { const line = new Date().toISOString()+' '+args.join(' ')+'\n'; fs.appendFileSync(_logFile, line); console.log(...args); }
const { execFile, spawn } = require('child_process');
const { PassThrough } = require('stream');
const { getBin } = require('./binPath');
const {
  joinVoiceChannel, getVoiceConnection, createAudioPlayer, createAudioResource,
  AudioPlayerStatus, VoiceConnectionStatus, entersState, StreamType
} = require('@discordjs/voice');

// ─── STATELESS UTILITIES ───

const JOKES = [
  "Why don't scientists trust atoms? Because they make up everything!",
  "What do you call a fish with no eyes? A fsh.",
  "Why did the scarecrow win an award? Because he was outstanding in his field.",
  "I'm reading a book about anti-gravity. It's impossible to put down.",
  "Did you hear about the mathematician who's afraid of negative numbers? He'll stop at nothing to avoid them.",
  "Why can't you give Elsa a balloon? Because she'll let it go.",
  "What do you call cheese that isn't yours? Nacho cheese.",
  "I would tell you a joke about construction, but I'm still working on it.",
  "Why did the bicycle fall over? Because it was two-tired.",
  "What's brown and sticky? A stick."
];

const EIGHTBALL = [
  'It is certain.', 'Without a doubt.', 'Yes, definitely.', 'Most likely.',
  'Signs point to yes.', 'Ask again later.', 'Cannot predict now.',
  'Concentrate and ask again.', "Don't count on it.", 'My reply is no.',
  'My sources say no.', 'Very doubtful.'
];

const RPS_WIN = { Rock: 'Scissors', Paper: 'Rock', Scissors: 'Paper' };

function normalizeDiscordEmoji(e) {
  if (!e) return e;
  const m = (e || '').match(/^<a?:(\w+):(\d+)>$/);
  return m ? `${m[1]}:${m[2]}` : e.trim();
}

// General fallback NSFW subreddits used when a category-specific sub returns nothing
const NSFW_FALLBACK_SUBS = ['gonewild','RealGirls','nsfw','nsfwgif','Amateur','normalnudes','amateurporn','GoneWildCurvy','SexyWomen'];

// Reddit fetch cache — shared by all callers (autopost + slash commands) to avoid redundant requests.
// A 4-minute TTL means autopost and back-to-back slash commands reuse the same JSON response.
const _redditRawCache = new Map(); // url → { raw: string, ts: number }
const _REDDIT_CACHE_TTL = 4 * 60 * 1000; // 4 minutes
let _redditBackoffUntil = 0; // epoch ms — all Reddit requests are skipped until this time after a 429

// Reddit RSS helpers — RSS endpoints bypass the NSFW auth restriction on the JSON API.
// Parses Reddit's RSS2 feed XML into an array of post objects.
function _parseRedditRss(xml) {
  const items = [];
  const itemRe = /<item>([\s\S]*?)<\/item>/g;
  let m;
  while ((m = itemRe.exec(xml)) !== null) {
    const body = m[1];
    const getTag = tag => {
      const r = new RegExp(`<${tag}(?:\\s[^>]*)?>([\\s\\S]*?)<\\/${tag}>`);
      const x = r.exec(body);
      return x ? x[1].replace(/<!\[CDATA\[|\]\]>/g, '').trim() : null;
    };
    const getAttr = (tag, attr) => {
      const r = new RegExp(`<${tag}(?:\\s[^>]*)?\\s${attr}="([^"]+)"`);
      const x = r.exec(body);
      return x ? x[1] : null;
    };
    const title    = getTag('title') || '';
    const link     = getTag('link') || getAttr('link', 'href') || '';
    const comments = getTag('comments') || '';
    const id       = (getTag('guid') || '').replace(/^t\d+_/, '');
    const created  = Math.floor(new Date(getTag('pubDate') || 0).getTime() / 1000);
    const sub      = (comments.match(/\/r\/([^/]+)/) || [])[1] || '';
    const thumbnail = getAttr('media:thumbnail', 'url') || getAttr('media:content', 'url') || '';
    const content  = getTag('content:encoded') || '';
    if (link) items.push({ title, link, comments, id, created, sub, thumbnail, content });
  }
  return items;
}

// Classify an RSS item into a post object suitable for NSFW commands.
function _classifyRssItem(item) {
  const { link, thumbnail, title, id, created, sub } = item;
  if (!link) return null;
  let url = link;
  if (/\.gifv(\?|$)/i.test(url)) url = url.replace(/\.gifv(\?|$)/i, '.gif$1');
  const type = _classifyUrl(url);
  if (type) return { url, type, title, sub, created, id };
  if (/redgifs\.com\/watch\//i.test(url)) return { url, type: 'redgif', title, sub, created, id };
  if (/reddit\.com\/(gallery\/|r\/.+\/comments\/)/i.test(url)) return null;
  if (thumbnail && /\.(jpg|jpeg|png|gif|webp)/i.test(thumbnail)) {
    return { url: thumbnail, type: 'image', title, sub, created, id };
  }
  return null;
}

// Pick a random post from RSS items matching the type filter and not already seen.
function _pickRssPost(items, typeFilter, seenSet) {
  const candidates = items.map(_classifyRssItem).filter(p => {
    if (!p) return false;
    if (!_typeMatchesFilter(p.type, typeFilter)) return false;
    if (_isMaleContent(p.title, p.sub)) return false;
    if (seenSet && seenSet.has(p.url)) return false;
    return true;
  });
  if (!candidates.length) return null;
  const pick = candidates[Math.floor(Math.random() * Math.min(candidates.length, 20))];
  if (seenSet && pick) seenSet.add(pick.url);
  return pick;
}

// Classify a post object from the redditporn.com ajax.php API into our internal format.
function _classifyRpPost(post, seenSet) {
  if (!post) return null;
  const { url, mp4, title, subreddit: sub, author, type: rtype, domain } = post;
  const id = String(post.id || url || mp4 || '');
  if (!id) return null;
  if (seenSet && seenSet.has(id)) return null;
  if (_isMaleContent(title, sub)) return null;

  // v.redd.it requires auth — skip
  if (domain === 'v.redd.it' || /v\.redd\.it/i.test(url || '')) return null;

  // Redgifs: direct CDN mp4 available → download with audio via sendVideo.
  // Use SD URL (XYZ.mp4) — .hd.mp4 URLs don't embed in Discord.
  if (domain === 'redgifs.com' || /redgifs\.com/i.test(url || '')) {
    if (seenSet) seenSet.add(id);
    if (mp4) {
      const sdMp4 = mp4.replace(/\.hd\.mp4(\?|$)/i, '.mp4$1');
      return { videoUrl: sdMp4, url: url || sdMp4, type: 'mp4', title, sub, author, id };
    }
    if (!url) return null;
    return { url, type: 'redgif', title, sub, author, id };
  }

  // Direct mp4 from any source
  if (mp4 && /\.mp4(\?|$)/i.test(mp4)) {
    if (seenSet) seenSet.add(id);
    return { videoUrl: mp4, url: url || mp4, type: 'mp4', title, sub, author, id };
  }

  // Animated GIF — redditporn.com returns type "gif", "animatedgif", or a direct .gif URL
  if (rtype === 'gif' || rtype === 'animatedgif' || /\.gif(\?|$)/i.test(url || '')) {
    if (!url) return null;
    if (seenSet) seenSet.add(id);
    return { url, type: 'gif', title, sub, author, id };
  }

  // Gallery (multiple images from a Reddit gallery post)
  if (Array.isArray(post.gallery) && post.gallery.length >= 2) {
    if (seenSet) seenSet.add(id);
    const items = post.gallery
      .filter(g => g && g.url)
      .map(g => ({ url: g.url, type: /\.gif(\?|$)/i.test(g.url) ? 'gif' : 'image' }));
    if (items.length >= 2) return { galleryItems: items, title, sub, author, id };
  }

  // Image
  if (rtype === 'image' || /(i\.(redd|imgur)\.it|\.(jpg|jpeg|png|webp))(\?|$)/i.test(url || '')) {
    if (!url) return null;
    if (seenSet) seenSet.add(id);
    return { url, type: 'image', title, sub, author, id };
  }

  return null;
}

const _rpCache = new Map();
const _RP_CACHE_TTL = 5 * 60 * 1000;

// Round-robin index per guild+category so successive calls cycle through different subreddits.
// Key: `${guildId}:${cat}`, value: current offset into the subreddit list.
// Loaded from disk so restarts don't reset back to the same first-batch subreddits.
const _nsfwSubIndex = _loadNsfwSubIdx();
// Per-category index for fetchReddtasticContent (no guildId available there).
const _reddtasticSubIndex = new Map();

// Fetches posts from redditporn.com ajax.php API — bypasses Reddit's NSFW auth restriction.
// subsSlice: pre-shuffled subset of subreddit names to query.
// mediaFilter: redditporn.com media type filter — 'gif', 'video', 'image', or comma-separated combo.
async function fetchRedditPorn(subsSlice, seenSet, mediaFilter) {
  const subList = (Array.isArray(subsSlice) ? subsSlice : [subsSlice]).filter(Boolean);
  if (!subList.length) return null;
  const media    = mediaFilter || 'video,gif,image,gallery';
  const sort     = ['hot', 'new', 'top'][Math.floor(Math.random() * 3)];
  const page     = 1;
  const subsParam = subList.join(',');
  const cacheKey  = `${subsParam}|${sort}|${page}|${media}`;
  const cached = _rpCache.get(cacheKey);
  if (cached && Date.now() - cached.ts < _RP_CACHE_TTL) {
    const shuffledPosts = [...cached.posts].sort(() => Math.random() - 0.5);
    let _rpFallback = null;
    for (const p of shuffledPosts) {
      const r = _classifyRpPost(p, seenSet);
      if (!r) continue;
      if (r.type !== 'redgif') return r;           // image / gif / mp4 — use immediately
      if (!_rpFallback) _rpFallback = r;            // bare watch link — keep as last resort
    }
    return _rpFallback;
  }

  const qs = new URLSearchParams({
    page: String(page), limit: '50',
    subs: subsParam,
    sort, dir: 'desc', t: 'all',
    media,
  });
  const url = `https://redditporn.com/ajax.php?${qs}`;
  const headers = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
    'Referer': 'https://redditporn.com/',
    'X-Requested-With': 'XMLHttpRequest',
    'Accept': 'application/json, text/javascript, */*; q=0.01',
    'Accept-Language': 'en-US,en;q=0.9',
    'sec-fetch-dest': 'empty',
    'sec-fetch-mode': 'cors',
    'sec-fetch-site': 'same-origin',
  };

  return new Promise(resolve => {
    const req = https.get(url, { headers }, res => {
      if (res.statusCode >= 400) {
        vlog(`[RedditPorn] HTTP ${res.statusCode} subs=${subsParam.slice(0, 60)}`);
        res.resume(); return resolve(null);
      }
      let d = ''; res.on('data', c => d += c);
      res.on('end', () => {
        try {
          const data = JSON.parse(d);
          const posts = data.posts || data.data || data.items || (Array.isArray(data) ? data : []);
          vlog(`[RedditPorn] OK subs=${subsParam.slice(0,40)} posts=${posts.length}`);
          _rpCache.set(cacheKey, { posts, ts: Date.now() });
          const shuffledPosts = [...posts].sort(() => Math.random() - 0.5);
          let _rpFallback = null;
          for (const p of shuffledPosts) {
            const r = _classifyRpPost(p, seenSet);
            if (!r) continue;
            if (r.type !== 'redgif') return resolve(r);
            if (!_rpFallback) _rpFallback = r;
          }
          resolve(_rpFallback);
        } catch { resolve(null); }
      });
    });
    req.on('error', e => { vlog(`[RedditPorn] network error: ${e.message}`); resolve(null); });
    req.setTimeout(10000, () => { req.destroy(); vlog('[RedditPorn] timeout'); resolve(null); });
  });
}

// Fetch an embeddable post from the provided subreddits.
// typeFilter: 'image' | 'gif' | 'video' | undefined (any embeddable)
// Returns { url, type, sub, link } — type is 'image'|'gif'|'mp4'|'redgif'
// v.redd.it (auth-gated) and gifv (Imgur wrapper) are excluded. redgifs.com returns 'redgif' and is sent as plain content.
function _classifyUrl(url) {
  if (!url) return null;
  if (/v\.redd\.it/i.test(url)) return null;
  if (/\.gifv(\?|$)/i.test(url)) return null;
  // i.redgifs.com and thumbs CDN URLs are direct mp4s — handle as mp4 so sendVideo downloads them correctly.
  // The generic redgifs.com check must come after this or it would mis-type them as 'redgif'.
  if (/(?:i|thumbs\d*)\.redgifs\.com\//i.test(url) && /\.mp4(\?|$)/i.test(url)) return 'mp4';
  if (/redgifs\.com/i.test(url)) return 'redgif';
  if (/\.mp4(\?|$)/i.test(url)) return 'mp4';
  if (/\.gif(\?|$)/i.test(url)) return 'gif';
  if (/(i\.(redd|imgur)\.it|\.(jpg|jpeg|png|webp))(\?|$)/i.test(url)) return 'image';
  return null;
}

// Calls the Redgifs v2 API to get the direct HD mp4 CDN URL for a watch-page link.
// Returns the mp4 URL string, or null on failure.
async function fetchRedgifsUrl(watchUrl) {
  const m = watchUrl && (
    watchUrl.match(/redgifs\.com\/(?:watch|ifr)\/([a-zA-Z0-9]+)/i) ||
    watchUrl.match(/(?:i|thumbs\d*)\.redgifs\.com\/([a-zA-Z0-9]+)/i)
  );
  if (!m) return null;
  const id = m[1].toLowerCase();
  const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36';

  const bearer = await _getRedgifsToken();
  return new Promise(resolve => {
    const headers = { 'User-Agent': UA, 'Accept': 'application/json' };
    if (bearer) headers['Authorization'] = `Bearer ${bearer}`;
    const req = https.get(`https://api.redgifs.com/v2/gifs/${id}`, { headers }, res => {
      let d = ''; res.on('data', c => d += c);
      res.on('end', () => {
        try {
          const data = JSON.parse(d);
          const hd = data.gif?.urls?.hd || null;
          const sd = data.gif?.urls?.sd || null;
          resolve((hd || sd) ? { hd, sd } : null);
        } catch { resolve(null); }
      });
    });
    req.on('error', () => resolve(null));
    req.setTimeout(8000, () => { req.destroy(); resolve(null); });
  });
}

// Shared Redgifs temporary token — fetched once and cached for ~23 hours.
let _redgifsToken = '';
let _redgifsTokenExpiry = 0;
// Global rate limit — set to future epoch ms when Redgifs returns 429. All requests skip until clear.
let _redgifsRateLimitUntil = 0;
// Niche response cache — avoids hammering the API on repeated commands. TTL 10 min.
const _redgifsNicheCache = new Map(); // slug → { gifs: GifObject[], ts: number }
const _RGIFS_CACHE_TTL = 10 * 60 * 1000;
// Gifreels tag slug cache — site is Astro SSG so content changes infrequently. TTL 30 min.
const _gifreelsTagCache = new Map(); // tag → { slugs: string[], ts: number }
const _GIFREELS_CACHE_TTL = 30 * 60 * 1000;
// Maps our command categories to gifreels.com tag slugs.
// Tags are tightly scoped to what each command searches for — no off-topic tags.
// Multi-word tags use hyphens: big-ass, yoga-pants, etc.
// Each command maps to exactly ONE Gifreels tag page (/tag/{slug}/).
// Only content from that specific tag is fetched — no cross-contamination between commands.
const GIFREELS_CAT_TAG = {
  ass:         'ass',
  pussy:       'pussy',
  boobs:       'boobs',
  blowjob:     'blowjob',
  thick:       'thick',
  blonde:      'blonde',
  brunette:    'brunette',
  petite:      'petite',
  asian:       'asian',
  redhead:     'redhead',
  milf:        'milf',
  dp:          'double-penetration',
  cosplay:     'cosplay',
  leggings:    'leggings',
  nudes:       'nude',
  cum:         'cumshot',
  anal:        'anal',
  feet:        'feet',
  bondage:     'bondage',
  lesbian:     'lesbian',
  latina:      'latina',
  teen:        'teen',
  riding:      'riding',
  squirt:      'squirting',
  goth:        'goth',
  trans:       'tgirl',
  ebony:       'ebony',
  thighs:      'thighs',
  lingerie:    'lingerie',
  outdoor:     'outdoor',
  doggystyle:  'doggystyle',
  joi:         'joi',
  hentai:      'hentai',
  bbw:         'bbw',
  titfuck:     'titfuck',
  handjob:     'handjob',
  gangbang:    'gangbang',
  creampie:    'creampie',
  pov:         'pov',
  massage:     'massage',
  ahegao:      'ahegao',
  latex:       'latex',
  femdom:      'femdom',
  facesitting: 'facesitting',
  rimjob:      'rimjob',
  'nsfw-gif':  'hardcore',
  'nsfw-video':'hardcore',
};

// Fetch a video post from gifreels.com for a given command category.
// Fetches pages 1-3 for a ~3× larger pool and cycles through them sequentially
// via _nsfwSubIndex so the same slug is never repeated until the full list is exhausted.
// Returns { url, videoUrl, type:'gifreels', sub:'gifreels' } or null.
async function fetchGifreelsContent(cat, seenSet) {
  const tag = GIFREELS_CAT_TAG[cat];
  if (!tag) return null;
  const cached = _gifreelsTagCache.get(tag);
  let slugs;
  if (cached && Date.now() - cached.ts < _GIFREELS_CACHE_TTL) {
    slugs = cached.slugs;
  } else {
    const dedup = new Set();
    const items = [];
    for (let page = 1; page <= 3; page++) {
      try {
        const pageUrl = page === 1
          ? `https://gifreels.com/tag/${encodeURIComponent(tag)}/`
          : `https://gifreels.com/tag/${encodeURIComponent(tag)}/?page=${page}`;
        const html = await new Promise(resolve => {
          const req = https.get(pageUrl, {
            headers: {
              'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
              'Accept': 'text/html',
            },
          }, res => {
            if (res.statusCode >= 400) { res.resume(); return resolve(''); }
            let d = ''; res.on('data', c => d += c); res.on('end', () => resolve(d));
          });
          req.on('error', () => resolve(''));
          req.setTimeout(10000, () => { req.destroy(); resolve(''); });
        });
        if (!html) break;
        const matches = [...html.matchAll(/href="\/@([^/]+)\/post\/([A-Za-z0-9_-]+)"/g)];
        let added = 0;
        for (const m of matches) {
          if (!dedup.has(m[2])) { dedup.add(m[2]); items.push({ slug: m[2], author: m[1] }); added++; }
        }
        vlog(`[Gifreels] tag="${tag}" page=${page} +${added} (total ${items.length})`);
        if (!added) break;
      } catch (e) { vlog(`[Gifreels] page ${page} error: ${e.message}`); break; }
    }
    slugs = items;
    if (slugs.length) _gifreelsTagCache.set(tag, { slugs, ts: Date.now() });
    vlog(`[Gifreels] tag="${tag}" ${slugs.length} slugs cached`);
  }
  if (!slugs || !slugs.length) return null;
  // Sequential rotation — cycles through the full list before repeating anything.
  const gfKey = `gifreels:${tag}`;
  const gfIdx = _nsfwSubIndex.get(gfKey) || 0;
  _nsfwSubIndex.set(gfKey, (gfIdx + 1) % slugs.length);
  const item = slugs[gfIdx % slugs.length];
  const videoUrl = `https://xcdn.tv/cdn/storage/production/gifreels/post/${item.slug}/gif.mp4`;
  const url = `https://gifreels.com/post/${item.slug}`;
  if (seenSet) { seenSet.add(item.slug); seenSet.add(url); seenSet.add(videoUrl); }
  vlog(`[Gifreels] idx=${gfIdx}/${slugs.length} slug="${item.slug}" tag="${tag}"`);
  return { url, videoUrl, type: 'gifreels', sub: 'gifreels', author: item.author || null };
}
// Maps command categories to subreddit names indexed by reddxxx.com sitemaps.
const REDDXXX_CAT_SUBS = {
  ass:         ['ass','AssAndTitties','BigBooty','TheBooty','BigAssGifs','PhatAssWhiteGirls','pawg','AssShaking','BootyShaking','GirlsWithBigButts','asshole'],
  pussy:       ['pussy','WetPussyClub','Eating_Pussy_GIFs','PussyEatingClub','girlsgonewild','gonewild','PussyLiquor'],
  boobs:       ['boobs','Boobies','BigNaturals','titties','TittyDrop','BustyPetite','BiggerThanYouThought','boobbouncing'],
  blowjob:     ['blowjob','oral','SuckingCock','Blowjobs','deepthroat','gagging','facefuck'],
  thick:       ['chubby','bbw','curvy','thick','BiggerThanYouThought','pawg'],
  blonde:      ['blonde','blondes','BlondeGirls','BlondePAWG','BlondesPorn','Blonde_Bombshells','HotBlondes_','smallblondies','blondesinblue','palegirls','Blonde','BlondeGoneWild'],
  brunette:    ['brunette','brunettes','BrunetteCute','Brunette_Vixens','SexBrunette','DarkHairGirls','HotBrunettes','BrunetteGoneWild'],
  petite:      ['petite','smalltits','petitegonewild','PetiteGoneWild'],
  asian:       ['asian','AsianGifs','AsianHotties','EastAsians','AsianPorn','AsianNSFW'],
  milf:        ['milf','MILF','over30','cougars','MilfsLikeitBig'],
  dp:          ['threesome','dp','doublePenetration','SpitRoasted','AirTight'],
  cosplay:     ['cosplay','cosplaygirls','CosplayGirls'],
  leggings:    ['leggings','leggings_haven','Leggings_Gone_Wild','girlsinleggings','YogaPants','leggings_pussy_bulge','girlsinyogapants','lululemon','Tight_Leggings','Shinyleggings','hotgirlsinleggings','lululemonleggingz','leggingsMidSection','SeeThroughLeggings','socksoverleggings','yogapantsleggings','Leggingsandmore','HeelsandLeggings','cameltoeoriginals','ClothedCurves','sexy_girls_leggings','blackleggingslove','cumcoveredleggings','LeggingsSexy','LeggingsInPublic','SpandexLove','yogapantshumping'],
  nudes:       ['gonewild','amateur','nudes','RealGirls','normalnudes','nude','GoneWild'],
  cum:         ['cumshots','facials','CumSluts','creampie','CumFetish','cumswallow'],
  anal:        ['anal','AnalGW','AnalLovers','asshole','analcreampie'],
  feet:        ['feet','FootFetish','soles','girlswithfeet','feetpics'],
  bondage:     ['bondage','bdsm','BDSMcommunity','tied'],
  lesbian:     ['lesbians','girlkissing','lesbian','Eating_Pussy_GIFs','girlswithgirls'],
  latina:      ['latinas','latina','LatinasGW','LatinaNSFW'],
  teen:        ['collegesluts','Teens','TeensNSFW'],
  riding:      ['riding','CowgirlLovers','ReverseGifs','cowgirl'],
  squirt:      ['squirting','SquirtingGifs','gushing','SquirtingPorn'],
  goth:        ['goth','altgirls','alternativegirls','GothGirls'],
  trans:       ['transgender','trans','transporn','TransGoneWild','ShemaleGoneWilder','ThiccTransWomen','GoneWildTrans','EbonyTSLovers','LadyboyPorn','Tgirls','girlcock','TGirlSluts','Shemales','tspetite','trans_mommies','transgoddesses'],
  ebony:       ['ebony','EbonyGW','interracial','bbc','EbonyNSFW'],
  thighs:      ['thighs','legs','stockings','thighhighs','Thigh','pantyhose'],
  lingerie:    ['lingerie','stockings','Panties','Underwear','SexyLingerie'],
  outdoor:     ['public','PublicFlashing','outdoor','PublicSex'],
  doggystyle:  ['doggystyle','Doggystyle'],
  joi:         ['jerkoffencouragement','JOI','masturbation','joi'],
  hentai:      ['hentai','ecchi','rule34','Hentai','hentaivideos'],
  redhead:     ['redheads','gingers','RedheadGW','Redheads'],
  ahegao:      ['ahegao','orgasm','Ahegao','AhegaoGirls','RealAhegao','Ahegao_IRL','pornwhoreexpressions','HappyEmbarrassedGirls','Facialexpression','OFace','orgasmface'],
  bbw:         ['bbw','chubby','curvy','BiggerThanYouThought','BBW'],
  pov:         ['pov','POV_GW','POV'],
  creampie:    ['creampie','CreampieLovers','creampies','analcreampie'],
  titfuck:     ['titfuck','paizuri','Titfuck'],
  gangbang:    ['gangbang','threesome','Gangbang'],
  femdom:      ['femdom','FemdomCommunity','Femdom','femdomgonewild','FemdomHumiliation','AuthenticFemdom','CuteFemdom','Pegging','SheFucksHim','BallBusting','gentlefemdom','FemdomHandjob','femdom_gifs','dommes','Queening','SheDoesTheWork'],
  handjob:     ['handjob','edging','Handjob','GirlsFinishingTheJob','FemdomHandjob','heavenly_handjobs','handjobs','helpinghand','handjobkisses','CumExtractor','thatsthespot','MakingOff'],
  massage:     ['massage','soapymassage','MassagePorn','EroticMassage','MassageSexPorn','AsianMassagePorn','MassageTableNSFW','OilMassage','SensualMassage','happy_ending_GOAT','RubAndTug'],
  latex:       ['latex','fetish','LatexAndLeather','latexfetish','ShinyPorn','Hardcore_Latex','LatexLadies','Latex_porn','PVCGirls','CatsuitNSFW','shinybondage','GirlLatexSexy'],
  facesitting: ['facesitting','FaceSitting','FacesittingHub','FemdomFaceSitting','facesmothering','FacesittingPorn','Queening','SitOnYourFace','FacesittingDomminance','facesittinglovers'],
  rimjob:      ['rimjob','analingus','Rimjob','GirlsRimGuys','EdibleButtholes','RimmingGirls','Rimming_kingdom','AssLicking','EatMyAss','Analingus'],
  'nsfw-gif':  ['NSFW_GIF','nsfwgif','gonewild','NSFW','porn','sex','GIF'],
  'nsfw-video':['nsfwvideos','NSFW_GIF','porn','sex','gonewild','videos'],
};

// Sitemap page cache — page number → { entries: [{sub,postId,cdnUrl}], ts }
const _reddxxxSitemapCache = new Map();
const _REDDXXX_SITEMAP_TTL = 30 * 60 * 1000;
const _REDDXXX_SITEMAP_PAGES = 14;

async function _fetchReddxxxSitemap(page) {
  const cached = _reddxxxSitemapCache.get(page);
  if (cached && Date.now() - cached.ts < _REDDXXX_SITEMAP_TTL) return cached.entries;
  const xml = await new Promise((resolve, reject) => {
    const req = https.request({
      hostname: 'reddxxx.com',
      path: `/sitemap-videos/${page}`,
      method: 'GET',
      headers: {
        'User-Agent': 'Mozilla/5.0 (compatible; Googlebot/2.1; +http://www.google.com/bot.html)',
        'Accept': 'application/xml,text/xml,*/*',
      },
    }, res => {
      if (res.statusCode >= 400) { res.resume(); return reject(new Error(`HTTP ${res.statusCode}`)); }
      const chunks = []; res.on('data', c => chunks.push(c)); res.on('end', () => resolve(Buffer.concat(chunks).toString()));
    });
    req.on('error', reject);
    req.setTimeout(12000, () => { req.destroy(); reject(new Error('timeout')); });
    req.end();
  });
  const entries = [];
  const urlBlocks = xml.match(/<url>([\s\S]*?)<\/url>/g) || [];
  for (const block of urlBlocks) {
    const locM = block.match(/<loc>\s*https?:\/\/reddxxx\.com\/r\/([^\/]+)\/comments\/([a-z0-9]+)\/[^<]*\s*<\/loc>/i);
    if (!locM) continue;
    const cdnM = block.match(/<video:content_loc>\s*(https?:\/\/cdn\d*\.reddxxx\.com\/[^\s<]+)\s*<\/video:content_loc>/i);
    const imgM = block.match(/<(?:image:loc|video:thumbnail_loc)>\s*(https?:\/\/cdn\d*\.reddxxx\.com\/[^\s<]+\.(?:jpe?g|png|webp))\s*<\/(?:image:loc|video:thumbnail_loc)>/i);
    const cdnUrl = cdnM ? cdnM[1].trim() : (imgM ? imgM[1].trim() : null);
    entries.push({ sub: locM[1], postId: locM[2], cdnUrl });
  }
  if (entries.length) _reddxxxSitemapCache.set(page, { entries, ts: Date.now() });
  vlog(`[Reddxxx] sitemap page=${page} parsed ${entries.length} entries`);
  return entries;
}


function _headRequest(url) {
  return new Promise(resolve => {
    const parsed = new URL(url);
    const req = https.request(
      { hostname: parsed.hostname, path: parsed.pathname, method: 'HEAD',
        headers: { 'User-Agent': 'Mozilla/5.0', 'Referer': 'https://reddxxx.com/' } },
      res => { res.resume(); resolve(res.statusCode >= 200 && res.statusCode < 400); }
    );
    req.on('error', () => resolve(false));
    req.setTimeout(6000, () => { req.destroy(); resolve(false); });
    req.end();
  });
}

// Fetch reddxxx content directly from cdn*.reddxxx.com using their video sitemap.
// Falls back to redditporn.com with reddxxx subs if no sitemap match is found.
async function fetchReddxxxContent(cat, seenSet) {
  const subs = REDDXXX_CAT_SUBS[cat];
  if (!subs || !subs.length) return null;
  const subsSet = new Set(subs.map(s => s.toLowerCase()));
  // Try up to 4 random sitemap pages for matching CDN entries.
  const pages = [];
  for (let i = 1; i <= _REDDXXX_SITEMAP_PAGES; i++) pages.push(i);
  pages.sort(() => Math.random() - 0.5);
  for (const page of pages.slice(0, 4)) {
    let entries;
    try { entries = await _fetchReddxxxSitemap(page); } catch { continue; }
    if (!entries || !entries.length) continue;
    const matching = entries.filter(e => {
      if (!e.cdnUrl) return false;
      // cdn4 and below are unreachable — only cdn5+ work
      const cdnNumM = e.cdnUrl.match(/cdn(\d+)\.reddxxx\.com/i);
      if (cdnNumM && parseInt(cdnNumM[1], 10) < 5) return false;
      if (!subsSet.has(e.sub.toLowerCase())) return false;
      if (seenSet && seenSet.has(e.cdnUrl)) return false;
      return true;
    });
    if (!matching.length) continue;
    matching.sort(() => Math.random() - 0.5);
    const pick = matching[Math.floor(Math.random() * Math.min(matching.length, 20))];
    const isVideo = /\.mp4(\?|$)/i.test(pick.cdnUrl);
    const isImg   = /\.(jpe?g|png|webp)(\?|$)/i.test(pick.cdnUrl);
    if (!isVideo && !isImg) continue;
    if (seenSet) seenSet.add(pick.cdnUrl);
    vlog(`[Reddxxx] CDN page=${page} sub="${pick.sub}" url="${pick.cdnUrl}"`);
    const pageUrl = `https://reddxxx.com/r/${pick.sub}/comments/${pick.postId}/`;
    return { url: pageUrl, videoUrl: isVideo ? pick.cdnUrl : undefined, type: isVideo ? 'mp4' : 'image', sub: pick.sub, source: 'reddxxx' };
  }
  // Fallback: redditporn.com with reddxxx subreddit list
  const rxKey = `reddxxx:${cat}`;
  const rxIdx = _nsfwSubIndex.get(rxKey) || 0;
  const batch = [];
  for (let i = 0; i < 8; i++) batch.push(subs[(rxIdx + i) % subs.length]);
  _nsfwSubIndex.set(rxKey, (rxIdx + 8) % subs.length);
  vlog(`[Reddxxx] CDN miss, fallback redditporn batch=[${batch.slice(0,3).join(',')}...]`);
  return fetchRedditPorn(batch, seenSet);
}

// Subreddit lists sourced from reddtastic.com's 700+ indexed NSFW subreddit directory.
// Each command maps to the most relevant subs from that directory.
const REDDTASTIC_CAT_SUBS = {
  ass:         ['ass','asstastic','BigBooty','TheBooty','PhatAssWhiteGirls','pawg','BigAss','BubbleButts','booty','AssAndTitties','GrabDatAss','AwesomeAss','CuteLittleButts','BootyShaking','AssClappersINC','Backview','WomenBendingOver','rice_cakes','OiledAss','PawgRiding','FAWGs','ClappingDemCheeks','DumptruckBootys','Wifebutt','phatassvideo','BlondePAWG','whooties','GoonForAss'],
  pussy:       ['pussy','WetPussyClub','Spreadopenpussies','MeatyVaginas','HotWetPussy','Eating_Pussy_GIFs','Beautifulbaldpussy','PussyPerfectionX','shavedpussies','Innie','inniepussygirls','hugelabialove','Creaming','grool','phatpussy','GodPussy','PinkishPussy','Pussy_Perfection','PussyFinish','youngpussylips','cameltoeoriginals','rearpussy','ButterflyWings','bigclit','LabiaGW'],
  boobs:       ['boobs','tits','TittyDrop','BigNaturals','Boobies','YGWBT','boobbounce','BiggerThanYouThought','hugenaturals','BustyNaturals','homegrowntits','Nipples','largemilkers','AdorableBoobs','FantasticBreasts','OnlyNaturalBoobs','2busty2hide','BreastExpansion','B_Cups','RetrousseTits','Nipslips_NSFW','biggerthanherhead','BigTitsHeaven','HugeBoobsNatural','Saggytit','naturaltitties','Saggy','ghostnipples','bigareolas'],
  blowjob:     ['Blowjobs','BlowJob','deepthroat','FaceFuck','throatpussy','SuctionBlowjobs','HeadCrazy','BallsDeepThroat','SorryCantTalk','EliteBlowjob','gawkgawkgawk','DeepThroatTears','gaggingwhores','POVSUCK','BestBlowjob','BlowjobGradeA','HungryForCock','ShutMouthAndSuckDick','LuckyDick','BlowjobSkills','DiligentBlowjob','Softsuck','PushHerHead','AsianBlowjobs','PublicBlowjobs','EbonyThroatQueens','FantasticBlowjob','ignoredblowjobs','AssUpBJ'],
  thick:       ['thick','curvy','ThickchicksGW','ThicknessAppreciaton','sensualcurves','thickwhitegirls','Thick_and_Delicious','CurvyWhiteGirls','SlimThick','Break_Yo_Dick_Thick','offseasonthickness2','ThickSloppyCreamy','FupaLuv','pawg','mombod','ThickCurvyExotic','thicksub'],
  blonde:      ['Blonde','HotBlondes_','BlondePAWG','BlondesPorn','Blonde_Bombshells','smallblondies','blondesinblue','palegirls','Babes','bigtitsblonde','BlondeGoneWild','SexyBlondes','NaturalBlondes','BlondeNudes','BlondeAssAndBoobs','blondes','BeautifulBlondes','BlondeGirls'],
  brunette:    ['brunette','BrunetteCute','Brunette_Vixens','SexBrunette','DarkHairGirls','HotBrunettes','BrunetteGoneWild','sexyhair','brunettes','BrunettePorn','BrunetteBeauties','BrunetteNSFW','BrunettesNaked','DarkHairNSFW'],
  petite:      ['petite','PetiteGoneWild','xsmallgirls','PocketSizedSluts','TinySizeQueens','HornyPetiteTeenGirls','BustyPetite','SmallAsian','dirtysmall','TinyTits','PetiteTits','A_Cups','smallboobs','smalltitsbigass'],
  asian:       ['AsiansGoneWild','AsianFetish','AsianHotties','jav','UncensoredAsian','AsianNSFW','AsianCumsluts','AsianBlowjobs','twitchasians','JapanesePorn2','Koreanhottiesreal','rice_cakes','juicyasians','nextdoorasians','paag','JapaneseKissing','NSFW_China','javdreams'],
  milf:        ['milf','MILF','clubmilfs','MommyHeaven','CougarsForCubs','maturemilf','HotMoms','MilfBody','amateur_milfs','Perv_Mom','sexiestmilfs','gilf','gonewild30plus','40plusGoneWild','Millennials_Gone_Wild','milfcumsluts','slut_MILFs','Milfie'],
  dp:          ['DP_doublepenetration','doublevaginal','doubleanal','SpitRoasted','AirTight','dpforher','DoublePenetrationLove','Triplepenetration'],
  cosplay:     ['cosplaygirls','nsfwcosplay','CosplayNSFW_','CosplayPornVideos','CosplayGirlsNSFW','NudeCosplay','CosplayLewd','GoonToCosplay','EGirls','SchoolgirlsXXX','Maidsex','cosplayonoff','cosplaybutts'],
  leggings:    ['leggings','leggings_haven','Leggings_Gone_Wild','girlsinleggings','YogaPants','leggings_pussy_bulge','girlsinyogapants','lululemon','Tight_Leggings','Shinyleggings','hotgirlsinleggings','lululemonleggingz','leggingsMidSection','SeeThroughLeggings','socksoverleggings','yogapantsleggings','Leggingsandmore','HeelsandLeggings','cameltoeoriginals','ClothedCurves','sexy_girls_leggings','blackleggingslove','cumcoveredleggings','LeggingsSexy','LeggingsInPublic','SpandexLove','yogapantshumping'],
  nudes:       ['gonewild','RealGirls','normalnudes','AmIFuckWorthy','Nude_Selfie','NudeGirlsHub','MirrorSelfie','AmateurPornGW','GirlsGW','Sextrophies','averagegirls','BestGirlsGoneWild','FreeNudesGW','NudeNonNude','Nudes','Naked','NSFWverifiedamateurs','GWCouples','Amateur','HomemadeNsfw','homesex'],
  cum:         ['cumsluts','Facials','cumshots','CumCoveredSluts','GirlsFinishingTheJob','CumSwallowing','cumontongue','cumshotgifs','cum_on_tits','amateurcumsluts','MassiveFacial_EpicCum','ThrobbingCIM','BestAmateurCumshots','Hyperspermia','CumOverdose','CumShowers','PussyFinish','CumHaters','ballsdeepandcumming','milfcumsluts','bodyshots','Bukkake'],
  anal:        ['anal','AnalGW','LoveAnal','upherbutt','AssHoleGW','Deep_Anal','buttsex','buttplug','AnalDildoGirls','HoleWreckers','BackdoorBeauties','CloseUpAnalSex','analcreampies','AnalGape','AnalStretching','BBWAnal','NotInThePussy','AssCracked','TightAnal','doubleanal','Roughanal','SurpriseAnal','assholegonewild'],
  feet:        ['feet','VerifiedFeet','FeetInYourFace','solesandface','FootjobCum','feetqueengirls','FeetFootKink','EgirlFeet','ButtsAndBareFeet','TikTokFeet','MissionarySoles','AnimeFeets','Rate_my_feet'],
  bondage:     ['Bondage','bdsm','BDSMGW','BDSMcommunity','Dominated','ForcedOrgasms2','RuinedOrgasms','collared','freeuse','BondageBlowjobs','chastity','orgasmcontrol','StuckHentai','ExtremeFetishes','hentaibondage'],
  lesbian:     ['lesbians','GirlsWithGirls','LesbianGirlsPorn','girlskissing','BestLesbianNSFW','LesbianFantasy','LesbianDrip','scissoring','HDLesbianGifs','JustFriendsHavingFun','MoreThanFriends','lesdom','LesbianSpitKissing','LesbiansMate','BlackGirlsKissing','StraightGirlsPlaying','LesbianGoonette','CuteLesbians'],
  latina:      ['latinas','LatinaGoneWild','LatinasNSFW','LatinaHotties','SexyLatinas','latinasgw','hotlatinas','ThickLatinas','esposashotwife','ArgNSFW','Mexicana','tortas','CulosDeMexicanas','LatinaCuties','BrasiIeirasGostosas'],
  teen:        ['collegesluts','Gonewild18','legalteens','18_19','PetiteGoneWild','GirlsGW','TinyCuteTeen','tiny18_21','Teens18Plus','legaladults','18andAbove','YoungButLegal','EighteenPlus_','Coeds','CollegeGirls','teensGW','slutsover18','Younggirls18'],
  riding:      ['CowgirlRiders','SheFucksHim','GirlsOnTop','ridingcowgirl','Riding_Cock','POVCOWGIRL','Latinas_Riding','LipsThatGrip','PussyGripping','girlswhorides','ReverseCowgirl','POV_cowgirl','BigTitsRiding','PawgRiding','ridingxxx','Riding_bitches','SquattingOnDildos','riding_queens'],
  squirt:      ['squirting','SquirtGirls','squirtingvideos','SoloSquirters','bestsquirt','SquirtWhileFucked','PeeandSquirtGIFs','squirtingvideosNSFW','SquirtWhileFucked'],
  goth:        ['gothsluts','GothWhoress','bigtiddygothgf','altgonewild','EmoGirlsFuck','thickgothgirls','GothSlutsFuck','PunkGirls','EGirls','emogirls'],
  trans:       ['transporn','TransGoneWild','hornytrans','ShemaleGoneWilder','ThiccTransWomen','GoneWildTrans','EbonyTSLovers','LadyboyPorn','Tgirls','girlcock','TGirlSluts','Shemales','ShemalesParadise','dickgirls','tspetite','trans_mommies','transgoddesses','TSRidingWhileHard'],
  ebony:       ['Ebony','ebonyamateurs','ebonyhomemade','EbonyPussyOnly','BlackGirlsCentral','EbonyThroatQueens','africanbootymeat','BlackChicksBlackDicks','Blacktittyworld','BlackPornMatters','blackchickswhitedicks','ebonybaddiez','sexyblackfemale','EbonyCuties'],
  thighs:      ['Thigh','Thighs','thighhighs','stockings','pantyhose','fishnets','ThighHighSocks','GirlsInThighhighs','BootsAndLegs','Legs','thighlover','UpskirtPanties','lingeriewomen','thong'],
  lingerie:    ['lingerie','LingerieGW','NSFW_Lingerie','lingerieforsex','thong','Panties','CuteGirlsinPanties','nopanties','CrotchlessLingerie_GW','WivesInLingerie','SexyLingerie','stockings','pantyhose','FullBackPanties','AssholeBehindThong','thongbj','pantiesfuckvideos','PantiesReveal','fuckingpanties','LoungeUnderwearGW'],
  outdoor:     ['PUBLICNUDITY','OutdoorWhores','RiskyPorn','FlashingAndFlaunting','public','PublicBlowjobs','PublicSexPorn','Flashing','holdthemoan','Publicsex','exhibitionists','VoyeurFlash','NudeBeach_freaks','ChangingRooms','daresgonewild','FlashingGirls','CarSexPorn','SexInForest','FuckOutdoors','NSFW_Outdoors','awesomePublicNudity','cumminginpublic'],
  doggystyle:  ['DoggyStyle','Doggystyle_NSFW','DoggyStylePOV','SheLovesDoggy','pronebone','DoggystyleAllDay','ebony_doggystyle','Backshotssxxx','FromBehind','topdog_doggystyle','Latina_Doggy','DoggystylePosition','BackshotsFromBBC','Amateur_Doggy_Style'],
  joi:         ['joi','FullJOIs','JoiVids','JOI_femdom','girlsmasturbating','edging','masturbation','gettingherselfoff','SoloMasturbation','GirlMasturbations','MasturbationGoneWild','JackAndJill'],
  hentai:      ['hentai','rule34','ecchi','HENTAI_GIF','AnimePussy','AnimeBooty','AnimeTitties','HentaiBeast','HentaiBreeding','unstable_diffusion','sdnsfw','AIpornhub','FutanariHentai','FutanariGifs','hentaibondage','CartoonPorn','3DHentai','YuriHentai','OppaiHentai','thick_hentai','gangbanghentai','swimsuithentai','BimboHentai','EmbarrassedHentai'],
  redhead:     ['redheads','RedheadsPorn','redheadsfucking','GingerGirls','HotRedheads','FieryRedheads','NSFWRedheads','GingerNSFW','palegirls','redheadgoddesses','redheadgonewild'],
  ahegao:      ['AhegaoGirls','RealAhegao','Ahegao_IRL','pornwhoreexpressions','HappyEmbarrassedGirls','Facialexpression','ahegao','Ahegao','orgasmface','AhegaoFaces','DroolingSluts','OFacePorn','CumFaces','PleasureFaces','orgasm','OFace'],
  bbw:         ['BBW','chubby','BBW_Chubby','LoveBBWs','BreedingBBW','BBWHardcore','BBWPussys','FupaLuv','ChubbyGirlsGW','dirty_bbw','bbw_mommies','Fat_Fetish','ChubbyWomen','thickfat','femalefittofat'],
  pov:         ['HerPOV','POVPornVids','Povfuckin','femalepov','takerpov','DoggyStylePOV','POV_cowgirl','POVCOWGIRL','CheatingPOV'],
  creampie:    ['creampies','CreampiedAmateurs','BreedMeDaddy','DontPullOut','ForgotToPullOut','creampiegifs','CumPies','forcedcreampie','breeding_creampie','analcreampies','CumDumpsters','BreedingBBW','Breeding_her','BreedingMaterial','gloryholecreampie','FemdomCreampie','gothcreampies','CreampieCleanUp'],
  titfuck:     ['titfuck','tittyfucking','Paizuri','titfuckheaven','TitfuckBlowjob','ClothedTitfuck','cumcoveredtitfucking','Titfuckdicksuck','tittyfuck'],
  gangbang:    ['gangbang','GangbangChicks','GangbangZone','OrgyAndGroupSex','blowbang','Swingersgonewild','Orgy','Threesome','GroupSex','3somesAndMore','HotwifeSwingers','ReverseGangBangz','OrgySexPorn','MMFtrio','gangbreeding'],
  femdom:      ['Femdom','femdomgonewild','FemdomHumiliation','AuthenticFemdom','CuteFemdom','BallBusting','gentlefemdom','Pegging','SheFucksHim','dommes','FemdomHandjob','femdom_gifs','femdomcaptions','Queening','SheDoesTheWork'],
  handjob:     ['Handjob','GirlsFinishingTheJob','FemdomHandjob','handjobs','heavenly_handjobs','CumExtractor','thatsthespot','helpinghand','MakingOff','handjobkisses'],
  massage:     ['EroticMassage','MassageSexPorn','AsianMassagePorn','MassageTableNSFW','OilMassage','SensualMassage','happy_ending_GOAT','RubAndTug'],
  latex:       ['latexfetish','ShinyPorn','Hardcore_Latex','LatexLadies','Latex_porn','PVCGirls','CatsuitNSFW','shinybondage','GirlLatexSexy'],
  facesitting: ['facesitting','FacesittingHub','FemdomFaceSitting','facesmothering','FacesittingPorn','Queening','SitOnYourFace','FacesittingDomminance','facesittinglovers'],
  rimjob:      ['rimjob','GirlsRimGuys','EdibleButtholes','RimmingGirls','Rimming_kingdom','AssLicking','EatMyAss','Analingus','AssHoleGW'],
  'nsfw-gif':  ['NSFW_GIF','nsfw_gifs','porn_gifs','gifsgonewild','SexGifs','short_porn','RedGIFsAmateur','60fpsporn','OneMinutePorn','The_Best_NSFW_GIFS','Pornheat','hotclub','Sluttydreams','BestPornInGalaxy','porninfifteenseconds'],
  'nsfw-video':['short_porn','XxxHDVideos','porn','nsfw','HotNSFWvideo','OnlyVidsNSFW','HomemadeNsfw','AmateurVideos','CouplesAmateurPorn','RealCouplesPorn','long_porn','RedditNSFW','homemadexxx','FreePornSexVideo','60fpsporn'],
};
// Module-level subreddit lists — single source of truth used by both
// the slash command handler (NSFW_SUBS) and the autopost function (AP_CAT_SUBS).
const NSFW_CAT_SUBS = {
  ass: ['booty','Booty_Lovers','ButtsAndBareFeet','RateMyAss_','PawgLove','bigasses','AssClappersINC','BigButtAmateurs','asstastic','GoonForAss','ass','HugeTitsndAss','thickwhitegirls','FAWGs','HungryButts','Backview','twerking','Phatasswhitegirls','AssMasterpiece','Wifebutt','smalltitsbigass','SlimThick','BigAss','ClappingDemCheeks','BubbleButts','DumptruckBootys','pawg','WomenBendingOver','rice_cakes','phatassvideo','thick','whooties','OiledAss','PawgRiding','BlondePAWG','BoltedOnBooty','africanbootymeat','booty_queens','CuteLittleButts','AwesomeAss','GrabDatAss'],
  pussy: ['Pussy_Perfection','youngpussylips','pussyaddicts','MeatyVaginas','PussyPerfectionX','HotWetPussy','hugelabialove','Beautifulbaldpussy','WetPussys','cameltoeoriginals','vagina','HairyPussy','BBWPussys','pussy','Innie','phatpussy','Eating_Pussy_GIFs','Spreadopenpussies','inniepussygirls','ButterflyWings','Creaming','LoosePussyLand','GodPussy','needypussy','bigclit','grool','LabiaGW','rearpussy','shavedpussies','PussyFinish','PinkishPussy','asstopussy'],
  goth: ['EGirls','PunkGirls','gothsluts','tattooedgirls','GothWhoress','EmoGirlsFuck','gothgirlsgw','emogirls','bigtiddygothgf','altgonewild','thickgothgirls','GothSlutsFuck'],
  thick: ['bigasses','sensualcurves','curvy','HugeTitsndAss','thickwhitegirls','CurvyWhiteGirls','Stacked','Phatasswhitegirls','MassiveTitsnAss','SlimThick','ThickchicksGW','FupaLuv','pawg','mombod','thick','offseasonthickness2','MilfBody','ThickCurvyExotic','thicksub','ThicknessAppreciaton','ThickSloppyCreamy','Break_Yo_Dick_Thick','Thick_and_Delicious'],
  boobs: ['TittyDrop','FantasticBreasts','AdorableBoobs','BoobsNation','OnlyNaturalBoobs','boobs','PerfectTits','tits','B_Cups','ratemyboobs','BestTits','boobbounce','Nipples','RetrousseTits','homegrowntits','Nipslips_NSFW','BreastExpansion','BoobsAndTities','BigTitsDoggy','Boobies','BiggerThanYouThought','GrabHerTitties','largemilkers','BigTitsBigAreolas','BUSTYQUEENS','Busty_Girls','boltedontits','HugeBoobsNatural','hugenaturals','MassiveTitsnAss','BigTitsButClothed','BustyNaturals','BigTitsRiding','MacromastiaIRL','BigBoobsGW','bigtitsinbikinis','EngorgedVeinyBreasts','YGWBT','2busty2hide','BustyPetite','biggerthanherhead','BigTitsHeaven','hugeboobs','Saggytit','naturaltitties','bigareolas','Saggy','ghostnipples'],
  hentai: ['hentai','rule34','ecchi','doujinshi','HENTAI_GIF','AnimeBooty','AnimeTitties','AnimePussy','AnimeMILFS','AnimeFeets','BigAnimeTiddies','YuriHentai','FutanariHentai','FutanariGifs','hentaibondage','HentaiBeast','HentaiBreeding','HentaiVTuberGirls','HentaiPetgirls','CartoonPorn','3DHentai','3DPorncraft','SFMCompileClub','Overwatch_Porn','CyberPunkNsfw','AzurLewd','GenshinLewds','NikkeNSFW','NikkeMobile','MarvelRivalsR34nsfw','FortnitePornOnly','sex_comics','HonkaiStarRail34','OppaiHentai','OppaiLove','Waifus34','waifusgonewild','NintendoWaifus','ZeroTwoHentai','RavenNSFW','MakimaHentai','DemonSlayer34','NagatoroHentai','TsunadePorn','GanyuNSFW','HuTaoNSFW','ElfHentai','HelltakerHentai','FlatChestHentai','Tomboy_Hentai','swimsuithentai','pantsu','XrayHentai','Nekomimi','EmbarrassedHentai','BimboHentai','thick_hentai','gangbanghentai','Hololewd','loona_nsfw','spidergwen_34','MarinKitagawaR34','JerkOffToAnime','lewdgames','musclegirlart','Shadman','unstable_diffusion','sdnsfw','AIpornhub','AiUncensored','FutaAI','Artistic_Hentai'],
  blowjob: ['Blowjobs','BlowjobGirls','BlowJob','HeadCrazy','IWantToSuckCock','BlowJobsALLDay','SuctionBlowjobs','FaceFuck','throatpussy','BlowjobLovers','BallsDeepThroat','Suckers','deepthroat','SwordSwallowers','PublicBlowjobs','gawkgawkgawk','DeepThroatTears','JustSuckIt','AssUpBJ','EliteBlowjob','SlutMouth','SorryCantTalk','BlowjobGradeA','HungryForCock','ShutMouthAndSuckDick','BestBlowjob','LuckyDick','BlowjobInterview','BlowjobSkills','gaggingwhores','FantasticBlowjob','DiligentBlowjob','Softsuck','PushHerHead','DeepthroatTube','BondageBlowjobs','TitfuckBlowjob','POVSUCK','ignoredblowjobs'],
  lesbian: ['lesbianOral','JustFriendsHavingFun','GirlsWithGirls','LesbianGirlsPorn','Lesbian_gifs','girlskissing','CuteLesbians','lesbians','strapon_lesbians','LesbianDrip','MoreThanFriends','LesbianFantasy','lesdom','yuri','LesbianSpitKissing','scissoring','LesbianSloppyKisses','LesbiansMate','HDLesbianGifs','BlackGirlsKissing','StraightGirlsPlaying','BestLesbianNSFW','LesbianGoonette'],
  cum: ['cumsluts','RedditorCum','CumCoveredSluts','coveredincum','CumCannonAddicts','Facials','cumshots','fantasticfacials','GirlsFinishingTheJob','PrettyLittleCumsluts','AsianCumsluts','BimboCumsluts','CumSwallowing','cumonclothes','cumontongue','cumshotgifs','Hyperspermia','CumOverdose','CumAward','CumShowers','CumVulcan','CumBonus','BestAmateurCumshots','MassiveFacial_EpicCum','PussyFinish','CumHaters','CumSqueezer','ballsdeepandcumming','cumswallowingmovies','amateurcumsluts','ThrobbingCIM','AccidentalCumInMouth','CumshotConnoisseurs','milfcumsluts','cum_on_tits','bodyshots','Bukkake','CumTornado','PressCUMference','SuperCuteBabesJizzed','CumDumpsters'],
  feet: ['ButtsAndBareFeet','FeetInYourFace','VerifiedFeet','solesandface','EgirlFeet','Foot_Island','Rate_my_feet','TikTokFeet','AnimeFeets','FootjobCum','MissionarySoles','feet','FeetFootKink','feetqueengirls'],
  thighs: ['Thigh','thighhighs','Thighs','stockings','fishnets','pantyhose','thong','lingeriewomen','UpskirtPanties','ThighHighSocks','BootsAndLegs','Legs','GirlsInThighhighs','thighlover'],
  nudes: ['AmIFuckWorthy','AdorableNudes','Nude_Selfie','Naked','Nudes','NudeGirlsHub','MirrorSelfie','normalnudes','gonewild','PetiteGoneWild','collegesluts','RealHomePorn','Couplesporn','GirlsGW','needysluts','HomemadeNsfw','AmateurPornGW','NSFWverifiedamateurs','Sextrophies','averagegirls','Normalnudesgonewild','BritishNaughtyBits','GWCouples','RealGirls','homesex','AmateurHallofFame','BestGirlsGoneWild','casualnudity','RealCouplesPorn','Amateur','NudeNonNude','FreeNudesGW'],
  milf: ['clubmilfs','MommyHeaven','CougarsForCubs','Moms_In_Thongs','milf','maturemilf','momnsfw','MILFs','mombod','Milfie','HotMoms','MilfBody','amateur_milfs','Perv_Mom','milfcumsluts','obsf','Millennials_Gone_Wild','gilf','40plusGoneWild','AgeGapOldYoungNSFW','gonewild30plus','OldYoungTabooPorn','slut_MILFs','sexiestmilfs'],
  ebony: ['Blacktittyworld','ebonyhomemade','BlackPornMatters','blackchickswhitedicks','ebonyamateurs','ebonybaddiez','BlackGirlsCentral','EbonyPussyOnly','sexyblackfemale','SuperSizedEbonyLovers','EbonyCuties','Blackcelebrity','EbonyThroatQueens','Ebony','africanbootymeat','BlackChicksBlackDicks'],
  asian: ['AsiansGoneWild','AsianFetish','SubmissiveAsianSluts','asiangirls4whitecocks','nextdoorasians','AsianHotties','jav','UncensoredAsian','paag','rice_cakes','asiangirlswhitecocks','juicyasians','AsianBlowjobs','AsianNSFW','AsianCumsluts','javdreams','AsianTikTokGirls','NSFW_China','JapanesePorn2','twitchasians','Koreanhottiesreal','JapaneseKissing'],
  redhead: ['redheads','redheadgoddesses','RedheadsPorn','redheadsfucking','GingerGirls','HotRedheads','FieryRedheads','redheadgonewild','NSFWRedheads','GingerNSFW','palegirls'],
  ahegao: ['AhegaoGirls','RealAhegao','pornwhoreexpressions','HappyEmbarrassedGirls','Facialexpression','Ahegao_IRL'],
  anal: ['AssHoleGW','upherbutt','AssholesHD','LoveAnal','AnalDildoGirls','asshole','Deep_Anal','AnalGW','anal_gifs','AnalGape','AnalStretching','buttsex','buttplug','SpreadEm','BBWAnal','HoleWreckers','AssholeBehindThong','BackdoorBeauties','NotInThePussy','AssCracked','AnalAtLast','IntoHerAss','AnalEcstasy','CloseUpAnalSex','AnalBliss','anal','ProneBoneAnal','doubleanal','Roughanal','TightAnal','assholegonewild','analcreampies','SurpriseAnal'],
  bondage: ['Bondage','bdsm','BDSMGW','BDSMcommunity','Dominated','ForcedOrgasms2','RuinedOrgasms','Fisting','collared','chastity','ChastityCouples','BrokenBabesIsBack','BallBusting','orgasmcontrol','StuckHentai','CockWarming','freeuse','freeuseFonM','ExtremeFetishes','hentaibondage','BondageBlowjobs'],
  latina: ['esposashotwife','Mexicana','latinas','tortas','ArgNSFW','CulosDeMexicanas','LatinaCuties','latinchickswhitedicks','CelebsBR','deusasbrazil','AutumnFalls','BrasiIeirasGostosas','LatinaGoneWild','SexyLatinas','LatinasNSFW','LatinaHotties','latinasgw','hotlatinas','ThickLatinas'],
  petite: ['PetiteGoneWild','petite','TinyCuteTeen','OnlyFansPetite','xsmallgirls','tiny18_21','HornyPetiteTeenGirls','BustyPetite','SmallAsian','dirtysmall','smallboobs','A_Cups','B_Cups','aa_cups','smalltitsbigass','PetiteTits','CelebsWithPetiteTits','TinyTits','PocketSizedSluts','TinySizeQueens'],
  blonde: ['Blonde_Bombshells','palegirls','BeautifulAndNaked','Blonde','HotBlondes_','BlondesPorn','BlondePAWG','blondesinblue','smallblondies'],
  brunette: ['brunette','sexyhair','BrunetteCute','Brunette_Vixens','SexBrunette','DarkHairGirls','HotBrunettes','BrunetteGoneWild'],
  bbw: ['chubby','BBW_Chubby','BBW','LoveBBWs','Fat_Fetish','ChubbyWomen','BreedingBBW','thickfat','BBWHardcore','BBWPussys','ThickchicksGW','chubbypretzels','FupaLuv','femalefittofat','BBWAnal','ChubbyGirlsGW','dirty_bbw','bbw_mommies'],
  trans: ['transporn','TransGoneWild','Shemale_Big_Cock','hornytrans','Femcock','ShemaleGoneWilder','ShemalesCock','SheIsBigger','transboobs','elitetransporn','awesometransgirls','TransAngel','VenusTrans','Tsasshole','ThiccTransWomen','TransBootyShaking','GoneWildTrans','EbonyTSLovers','dickgirls','Shemales','ShemalesParadise','ChickWithDick','TS_Porn','AwesomeShemales','SheBussy','ShemaleAddiction','TSonFM','TSRidingWhileHard','ShemaleFuckingMale','tspetite','LadyboyPorn','TgirlsCum','bigdickgirl','Ladyboys','Tgirls','girlcock','TGirlSluts','trans_mommies','transgoddesses'],
  pov: ['CheatingPOV','femalepov','DoggyStylePOV','POVPornVids','POV_cowgirl','HerPOV','Povfuckin','takerpov','GFEPorn','SheFucksHim'],
  creampie: ['CumDumpsters','BreedMeDaddy','BreedingBBW','Breeding_her','BreedingMaterial','DontPullOut','ForgotToPullOut','creampiegifs','CreampieCleanUp','CumPies','creampies','cuminsideme','forcedcreampie','gloryholecreampie','Creampie_Porn','FemdomCreampie','analcreampies','breeding_creampie','CreampiedAmateurs','gothcreampies'],
  squirt: ['squirtingvideos','SquirtGirls','squirting','SquirtWhileFucked','SoloSquirters','bestsquirt','squirtingvideosNSFW'],
  titfuck: ['titfuck','tittyfucking','Paizuri','titfuckheaven','tittyfuck','ClothedTitfuck','TitfuckBlowjob','Titfuckdicksuck','cumcoveredtitfucking'],
  dp: ['doublevaginal','SpitRoasted','Triplepenetration','doubleanal','AirTight','DP_doublepenetration','fist_and_dick_dp','dpforher','DoublePenetrationLove'],
  gangbang: ['OrgyAndGroupSex','blowbang','GangbangChicks','gangbang','ReverseGangBangz','Swingersgw','3somesAndMore','HotwifeSwingers','Swingersgonewild','groupsex_gw','OrgySexPorn','FunWithFriends','GangbangZone','gangbreeding','Orgy','Threesome','MMFtrio','GroupSex'],
  lingerie: ['thong','lingeriewomen','Moms_In_Thongs','UpskirtPanties','fishnets','stockings','SexyButNotNude','pantyhose','FullBackPanties','CuteGirlsinPanties','AssholeBehindThong','thongbj','lingerie','fuckingpanties','pantiesfuckvideos','NSFW_Lingerie','lingerieforsex','WivesInLingerie','CrotchlessLingerie_GW','Gorgeous_Lingerie','LoungeUnderwearGW','LingerieGW','PantiesReveal','UnderwearGW'],
  cosplay: ['EGirls','SchoolgirlsXXX','CosplayPornVideos','cosplaygirls','Maidsex','NudeCosplay','nsfwcosplay','teachersgonewild','MarinKitagawaR34','HentaiSchoolGirls','MaidHentai','MyDressUpDarlingNSFW','CosplayNSFW_','CosplayLewd','CosplayGirlsNSFW','cosplayonoff','GoonToCosplay','cosplaybutts'],
  joi: ['girlsmasturbating','gettingherselfoff','SoloMasturbation','GirlMasturbations','MasturbationHentai','edging','joi','MasturbationGoneWild','JackAndJill','masturbation','FullJOIs','JoiVids','JOI_femdom'],
  femdom: ['Femdom','femdomgonewild','FemdomHumiliation','AuthenticFemdom','CuteFemdom','femdom_gifs','FemdomHandjob','femdomcaptions','BallBusting','gentlefemdom','FemdomCreampie','Dominated','Pegging','peggingfun','Pegging_Only','strapon_lesbians','SheFucksHim','SheDoesTheWork','Queening','dommes'],
  leggings: ['leggings','leggings_haven','Leggings_Gone_Wild','girlsinleggings','YogaPants','leggings_pussy_bulge','girlsinyogapants','lululemon','Tight_Leggings','Shinyleggings','hotgirlsinleggings','lululemonleggingz','leggingsMidSection','SeeThroughLeggings','socksoverleggings','yogapantsleggings','Leggingsandmore','HeelsandLeggings','cameltoeoriginals','ClothedCurves','sexy_girls_leggings','blackleggingslove','cumcoveredleggings','LeggingsSexy','LeggingsInPublic','SpandexLove','yogapantshumping'],
  riding: ['SheFucksHim','CowgirlRiders','SheDoesTheWork','BigTitsRiding','ridingxxx','PawgRiding','riding_queens','Riding_bitches','POV_cowgirl','girlswhorides','LipsThatGrip','GirlsOnTop','SheRidesIt','ridingcowgirl','SquattingOnDildos','Riding_Cock','POVCOWGIRL','Latinas_Riding','PussyGripping','Shefuckshimriding','ReverseCowgirl'],
  doggystyle: ['DoggyStyle','Doggystyle_NSFW','DoggyStylePOV','SheLovesDoggy','pronebone','ebony_doggystyle','topdog_doggystyle','Latina_Doggy','DoggystyleAllDay','Amateur_Doggy_Style','DoggystylePosition','Backshotssxxx','BackshotsFromBBC','FromBehind'],
  handjob: ['Handjob','GirlsFinishingTheJob','FemdomHandjob','helpinghand','CumExtractor','handjobs','thatsthespot','MakingOff','heavenly_handjobs','handjobkisses'],
  outdoor: ['PUBLICNUDITY','VoyeurFlash','OutdoorRecreation','OutdoorWhores','RiskyPorn','NudeBeach_freaks','FlashingAndFlaunting','public','ChangingRooms','PublicBlowjobs','PublicSexPorn','RealPublicNudity','Caught_in_public','workgonewild','daresgonewild','FlashingGirls','CarSexPorn','Flashing','holdthemoan','Publicsex','Exhibitionistfun','awesomePublicNudity','gwpublic','PublicFlashing','SexInForest','FuckOutdoors','NSFW_Outdoors','exhibitionists'],
  massage: ['EroticMassage','MassageSexPorn','AsianMassagePorn','happy_ending_GOAT','MassageTableNSFW','OilMassage','RubAndTug','SensualMassage'],
  latex: ['ShinyPorn','latexfetish','GirlLatexSexy','Hardcore_Latex','LatexLadies','shinybondage','Latex_porn','PVCGirls','CatsuitNSFW'],
  facesitting: ['facesitting','facesittinglovers','SitOnYourFace','FemdomFaceSitting','FacesittingDomminance','FacesittingHub','facesmothering','FacesittingPorn','Queening'],
  rimjob: ['rimjob','GirlsRimGuys','EdibleButtholes','AssHoleGW','RimmingGirls','Rimming_kingdom','AssLicking','EatMyAss','Analingus'],
  teen: ['collegesluts','Gonewild18','legalteens','18_19','PetiteGoneWild','GirlsGW','TinyCuteTeen','tiny18_21','Teens18Plus','legaladults','18andAbove','YoungButLegal','EighteenPlus_','Coeds','CollegeGirls','teensGW','slutsover18','Younggirls18'],
  'nsfw-gif': ['short_porn','Pornheat','RedGIFsAmateur','porn_gifs','hotclub','Sluttydreams','OneMinutePorn','The_Best_NSFW_GIFS','nsfw_gifs','60fpsporn','porninfifteenseconds','BestPornInGalaxy','PORN_GW','porn','NSFW_GIF','nsfw','NSFW_HTML5','Fucking_NSFW','gifsgonewild','SexGifs'],
  'nsfw-video': ['short_porn','Pornheat','XxxHDVideos','long_porn','porn_gifs','hotclub','nsfw_gifs','60fpsporn','BestPornInGalaxy','PORN_GW','porn','nsfw','NSFW_HTML5','HotNSFWvideo','OnlyVidsNSFW','FreePornSexVideo','RealHomePorn','RedditNSFW','AmateurVideos','HomemadeNsfw','homemadexxx','CouplesAmateurPorn','RealCouplesPorn'],
};

// Cache for reddtastic multi-subreddit Reddit feeds — TTL 8 min.
const _reddtasticCache = new Map();
const _REDDTASTIC_CACHE_TTL = 8 * 60 * 1000;

// Fetch content from Reddit's multireddit API using reddtastic.com's curated subreddit lists.
// Subreddit lists for Scrolller GraphQL API — each category maps to high-activity subreddits.
const SCROLLLER_CAT_SUBS = {
  ass:         ['ass','asstastic','BigBooty','pawg','PhatAssWhiteGirls','BigAss','booty','TheBooty','AssClappersINC','GrabDatAss'],
  pussy:       ['pussy','WetPussyClub','MeatyVaginas','HotWetPussy','Spreadopenpussies','WetPussys','phatpussy','cameltoeoriginals'],
  boobs:       ['boobs','TittyDrop','BigNaturals','tits','Boobies','YGWBT','hugenaturals','BustyNaturals','homegrowntits','BiggerThanYouThought'],
  blowjob:     ['Blowjobs','BlowJob','deepthroat','FaceFuck','throatpussy','gawkgawkgawk','HeadCrazy','POVSUCK'],
  thick:       ['thick','curvy','pawg','ThickchicksGW','thickwhitegirls','SlimThick','sensualcurves'],
  blonde:      ['Blonde','HotBlondes_','BlondePAWG','BlondesPorn','Blonde_Bombshells','blondes'],
  brunette:    ['brunette','BrunetteCute','Brunette_Vixens','DarkHairGirls','HotBrunettes'],
  petite:      ['petite','PetiteGoneWild','xsmallgirls','TinyCuteTeen','BustyPetite','TinyTits'],
  asian:       ['AsiansGoneWild','AsianFetish','AsianHotties','jav','UncensoredAsian','AsianNSFW','rice_cakes'],
  milf:        ['milf','MILF','clubmilfs','MommyHeaven','HotMoms','maturemilf','gonewild30plus'],
  dp:          ['DP_doublepenetration','doublevaginal','SpitRoasted','AirTight','doubleanal'],
  cosplay:     ['cosplaygirls','nsfwcosplay','CosplayNSFW_','CosplayGirlsNSFW','NudeCosplay'],
  leggings:    ['leggings','leggings_haven','Leggings_Gone_Wild','girlsinleggings','YogaPants','leggings_pussy_bulge','girlsinyogapants','lululemon','Tight_Leggings','Shinyleggings','hotgirlsinleggings','SeeThroughLeggings','cameltoeoriginals','sexy_girls_leggings','LeggingsSexy','LeggingsInPublic','SpandexLove','yogapantshumping'],
  nudes:       ['gonewild','RealGirls','normalnudes','Amateur','nsfw','GoneWild','Nudes','Naked','NudeGirlsHub'],
  cum:         ['cumsluts','Facials','cumshots','CumCoveredSluts','GirlsFinishingTheJob','CumSwallowing','Hyperspermia'],
  anal:        ['anal','AnalGW','LoveAnal','upherbutt','AnalGape','AnalStretching','asshole'],
  feet:        ['feet','VerifiedFeet','FeetInYourFace','solesandface','FootjobCum'],
  bondage:     ['Bondage','bdsm','BDSMGW','BDSMcommunity','freeuse'],
  lesbian:     ['lesbians','GirlsWithGirls','LesbianGirlsPorn','girlskissing','CuteLesbians','scissoring'],
  latina:      ['latinas','LatinaGoneWild','LatinasNSFW','LatinaHotties','SexyLatinas','hotlatinas'],
  riding:      ['CowgirlRiders','GirlsOnTop','ridingcowgirl','Riding_Cock','POVCOWGIRL','ReverseCowgirl'],
  squirt:      ['squirting','SquirtGirls','squirtingvideos','SoloSquirters','bestsquirt'],
  goth:        ['gothsluts','GothWhoress','altgonewild','bigtiddygothgf','EmoGirlsFuck'],
  trans:       ['TransGoneWild','transporn','Tgirls','ShemaleGoneWilder','girlcock','LadyboyPorn'],
  ebony:       ['ebony','EbonyGW','interracial','bbc','EbonyNSFW','africanbootymeat'],
  thighs:      ['thighs','thighhighs','stockings','pantyhose','Legs','GirlsInThighhighs'],
  lingerie:    ['lingerie','stockings','Panties','SexyLingerie','thong','UpskirtPanties'],
  ahegao:      ['AhegaoGirls','RealAhegao','Ahegao_IRL','pornwhoreexpressions'],
  redhead:     ['redheads','RedheadsPorn','GingerGirls','HotRedheads','FieryRedheads'],
  hentai:      ['hentai','HENTAI_GIF','rule34','ecchi','doujinshi','AnimeTitties'],
  pov:         ['POVPornVids','HerPOV','DoggyStylePOV','POV_cowgirl','femalepov'],
  creampie:    ['creampies','CreampiedAmateurs','BreedMeDaddy','DontPullOut','ForgotToPullOut'],
  titfuck:     ['titfuck','tittyfucking','Paizuri','titfuckheaven','TitfuckBlowjob'],
  gangbang:    ['gangbang','GangbangChicks','OrgyAndGroupSex','blowbang','Threesome'],
  femdom:      ['Femdom','femdomgonewild','FemdomHumiliation','AuthenticFemdom','SheFucksHim'],
  joi:         ['joi','girlsmasturbating','SoloMasturbation','FullJOIs','JoiVids'],
  bbw:         ['BBW','chubby','LoveBBWs','BBW_Chubby','Fat_Fetish','ChubbyWomen'],
  doggystyle:  ['DoggyStyle','Doggystyle_NSFW','DoggyStylePOV','pronebone','SheLovesDoggy'],
  handjob:     ['Handjob','GirlsFinishingTheJob','FemdomHandjob','helpinghand','handjobs'],
  outdoor:     ['PUBLICNUDITY','FlashingAndFlaunting','RiskyPorn','NudeBeach_freaks','PublicSexPorn'],
  massage:     ['EroticMassage','MassageSexPorn','OilMassage','AsianMassagePorn'],
  latex:       ['latexfetish','ShinyPorn','Hardcore_Latex','LatexLadies'],
  facesitting: ['facesitting','FemdomFaceSitting','FacesittingHub','Queening'],
  rimjob:      ['rimjob','GirlsRimGuys','AssLicking','EdibleButtholes'],
  teen:        ['collegesluts','Gonewild18','legalteens','18_19','GirlsGW','legaladults'],
  'nsfw-gif':  ['NSFW_GIF','nsfw_gifs','porn_gifs','SexGifs','60fpsporn','short_porn'],
  'nsfw-video':['short_porn','XxxHDVideos','porn','nsfw','HotNSFWvideo','OnlyVidsNSFW'],
};

// Fetch content from Scrolller's GraphQL API — a Reddit-content aggregator with direct media URLs.
// Uses POST to /api/v2/graphql; returns { url, videoUrl?, type, title, sub } or null on failure.
async function fetchScrolllerContent(cat, seenSet) {
  const subs = SCROLLLER_CAT_SUBS[cat];
  if (!subs || !subs.length) return null;
  const slKey = `scrolller:${cat}`;
  const slIdx = _nsfwSubIndex.get(slKey) || 0;
  _nsfwSubIndex.set(slKey, (slIdx + 1) % subs.length);
  const sub = subs[slIdx % subs.length];
  const query = `{ getSubreddit(url: "/r/${sub}") { children(iterator: null, limit: 30) { items { title mediaSources { url width height isMain } subredditTitle } } } }`;
  const bodyBuf = Buffer.from(JSON.stringify({ query }), 'utf8');
  return new Promise(resolve => {
    const req = https.request({
      hostname: 'scrolller.com',
      path: '/api/v2/graphql',
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        'Content-Length': bodyBuf.length,
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
        'Accept': 'application/json',
        'Origin': 'https://scrolller.com',
        'Referer': 'https://scrolller.com/',
      },
    }, res => {
      if (res.statusCode >= 400) { res.resume(); vlog(`[Scrolller] HTTP ${res.statusCode} r/${sub}`); return resolve(null); }
      let d = ''; res.on('data', c => d += c);
      res.on('end', () => {
        try {
          const json = JSON.parse(d);
          const items = json?.data?.getSubreddit?.children?.items || [];
          vlog(`[Scrolller] r/${sub} ${items.length} items`);
          const candidates = items.filter(item => {
            if (!item?.mediaSources?.length) return false;
            const src = item.mediaSources.find(s => s.isMain) || item.mediaSources[item.mediaSources.length - 1];
            return src?.url && (!seenSet || !seenSet.has(src.url));
          });
          if (!candidates.length) return resolve(null);
          const pick = candidates[Math.floor(Math.random() * Math.min(candidates.length, 20))];
          const src = pick.mediaSources.find(s => s.isMain) || pick.mediaSources[pick.mediaSources.length - 1];
          const url = src.url;
          if (seenSet) seenSet.add(url);
          const type = /\.mp4(\?|$)/i.test(url) ? 'mp4' : /\.gif(\?|$)/i.test(url) ? 'gif' : 'image';
          vlog(`[Scrolller] r/${sub} picked type=${type}`);
          resolve({ url, videoUrl: type === 'mp4' ? url : undefined, type, title: pick.title || null, sub: pick.subredditTitle || sub });
        } catch (e) { vlog(`[Scrolller] parse error: ${e.message}`); resolve(null); }
      });
    });
    req.on('error', e => { vlog(`[Scrolller] network error: ${e.message}`); resolve(null); });
    req.setTimeout(10000, () => { req.destroy(); vlog('[Scrolller] timeout'); resolve(null); });
    req.write(bodyBuf);
    req.end();
  });
}

// Reddtastic is a Reddit viewer/aggregator — their subreddit directory is the value; we hit Reddit directly.
// Returns { url, videoUrl?, type, title, sub, author } or null.
async function fetchReddtasticContent(cat, seenSet) {
  const subs = REDDTASTIC_CAT_SUBS[cat];
  if (!subs || !subs.length) return null;
  // Cycle 5 subs from the reddtastic curated list per call — different list from NSFW_CAT_SUBS.
  // Routes through redditporn.com which bypasses Reddit's NSFW auth requirement.
  const rtKey = `reddtastic:${cat}`;
  const rtIdx = _nsfwSubIndex.get(rtKey) || 0;
  const batch = [];
  for (let i = 0; i < 10; i++) batch.push(subs[(rtIdx + i) % subs.length]);
  _nsfwSubIndex.set(rtKey, (rtIdx + 10) % subs.length);
  vlog(`[Reddtastic] cat="${cat}" batch=[${batch.join(',')}]`);
  return fetchRedditPorn(batch, seenSet);
}

// reddvideo.tube — Reddit video aggregator with direct mp4 CDN links (media.reddit.tube).
// Each command maps to subreddit names that reddvideo.tube uses as category slugs.
const REDDVIDEO_CAT_SLUGS = {
  leggings:    ['leggings','leggings_haven','Leggings_Gone_Wild','girlsinleggings','YogaPants','leggings_pussy_bulge','girlsinyogapants','lululemon','Tight_Leggings','Shinyleggings','hotgirlsinleggings','SeeThroughLeggings','cameltoeoriginals','sexy_girls_leggings','LeggingsSexy','LeggingsInPublic','SpandexLove','yogapantshumping'],
  ass:         ['ass','BigBooty','pawg','PhatAssWhiteGirls','TheBooty','AssShaking','BigAss','booty','GrabDatAss','OiledAss','AssClappersINC','FAWGs','PawgRiding','AssAndTitties'],
  pussy:       ['pussy','WetPussyClub','MeatyVaginas','HotWetPussy','Eating_Pussy_GIFs','phatpussy','cameltoeoriginals','WetPussys'],
  boobs:       ['boobs','tits','TittyDrop','BigNaturals','Boobies','YGWBT','boobbounce','hugenaturals','BustyNaturals','Nipples','largemilkers'],
  blowjob:     ['Blowjobs','BlowJob','deepthroat','FaceFuck','gawkgawkgawk','HeadCrazy','POVSUCK','BestBlowjob','SuctionBlowjobs'],
  thick:       ['thick','curvy','pawg','thickwhitegirls','SlimThick','sensualcurves','ThickchicksGW','mombod'],
  blonde:      ['Blonde','HotBlondes_','BlondePAWG','BlondesPorn','Blonde_Bombshells','blondes','BlondeGirls','BlondeGoneWild'],
  brunette:    ['brunette','BrunetteCute','DarkHairGirls','HotBrunettes','brunettes','BrunettePorn'],
  petite:      ['petite','PetiteGoneWild','xsmallgirls','TinyTits','BustyPetite','PocketSizedSluts'],
  asian:       ['AsiansGoneWild','AsianHotties','jav','AsianNSFW','rice_cakes','AsianFetish','UncensoredAsian'],
  milf:        ['milf','MILF','clubmilfs','MommyHeaven','HotMoms','maturemilf','gonewild30plus','40plusGoneWild'],
  dp:          ['DP_doublepenetration','doublevaginal','SpitRoasted','AirTight','doubleanal','dpforher'],
  cosplay:     ['cosplaygirls','nsfwcosplay','CosplayGirlsNSFW','NudeCosplay','CosplayNSFW_','EGirls'],
  nudes:       ['gonewild','RealGirls','normalnudes','GoneWild','Amateur','Nudes','AmIFuckWorthy'],
  cum:         ['cumsluts','Facials','cumshots','CumSwallowing','GirlsFinishingTheJob','CumCoveredSluts'],
  anal:        ['anal','AnalGW','LoveAnal','upherbutt','AnalGape','AnalStretching','buttsex'],
  feet:        ['feet','VerifiedFeet','FeetInYourFace','solesandface','FootjobCum'],
  bondage:     ['Bondage','bdsm','BDSMGW','BDSMcommunity','freeuse'],
  lesbian:     ['lesbians','GirlsWithGirls','LesbianGirlsPorn','girlskissing','scissoring','CuteLesbians'],
  latina:      ['latinas','LatinaGoneWild','LatinasNSFW','LatinaHotties','SexyLatinas','hotlatinas'],
  teen:        ['collegesluts','Gonewild18','legalteens','18_19','GirlsGW','legaladults'],
  riding:      ['CowgirlRiders','GirlsOnTop','ridingcowgirl','Riding_Cock','POVCOWGIRL','ReverseCowgirl','PawgRiding'],
  squirt:      ['squirting','SquirtGirls','squirtingvideos','SoloSquirters','bestsquirt'],
  goth:        ['gothsluts','altgonewild','bigtiddygothgf','GothWhoress','EmoGirlsFuck'],
  trans:       ['TransGoneWild','transporn','Tgirls','ShemaleGoneWilder','girlcock','LadyboyPorn'],
  ebony:       ['ebony','EbonyGW','interracial','bbc','EbonyNSFW','africanbootymeat','Ebony'],
  thighs:      ['thighs','thighhighs','stockings','pantyhose','Legs','GirlsInThighhighs'],
  lingerie:    ['lingerie','stockings','Panties','SexyLingerie','thong','CuteGirlsinPanties'],
  ahegao:      ['AhegaoGirls','RealAhegao','Ahegao_IRL','pornwhoreexpressions'],
  redhead:     ['redheads','GingerGirls','HotRedheads','RedheadsPorn','FieryRedheads'],
  hentai:      ['hentai','HENTAI_GIF','rule34','ecchi','AnimeTitties','OppaiHentai'],
  pov:         ['POVPornVids','DoggyStylePOV','POV_cowgirl','femalepov','HerPOV'],
  creampie:    ['creampies','CreampiedAmateurs','DontPullOut','ForgotToPullOut'],
  titfuck:     ['titfuck','tittyfucking','Paizuri','TitfuckBlowjob'],
  gangbang:    ['gangbang','GangbangChicks','OrgyAndGroupSex','blowbang','Threesome'],
  femdom:      ['Femdom','femdomgonewild','FemdomHumiliation','AuthenticFemdom','SheFucksHim'],
  joi:         ['joi','girlsmasturbating','SoloMasturbation','FullJOIs','JoiVids'],
  bbw:         ['BBW','chubby','LoveBBWs','BBW_Chubby','Fat_Fetish'],
  doggystyle:  ['DoggyStyle','Doggystyle_NSFW','DoggyStylePOV','pronebone','SheLovesDoggy'],
  handjob:     ['Handjob','GirlsFinishingTheJob','FemdomHandjob','helpinghand','handjobs'],
  outdoor:     ['PUBLICNUDITY','FlashingAndFlaunting','RiskyPorn','NudeBeach_freaks','PublicSexPorn'],
  massage:     ['EroticMassage','MassageSexPorn','OilMassage','AsianMassagePorn'],
  latex:       ['latexfetish','ShinyPorn','Hardcore_Latex','LatexLadies'],
  facesitting: ['facesitting','FemdomFaceSitting','FacesittingHub','Queening'],
  rimjob:      ['rimjob','GirlsRimGuys','AssLicking','EdibleButtholes'],
  'nsfw-gif':  ['NSFW_GIF','nsfw_gifs','porn_gifs','SexGifs','60fpsporn','short_porn'],
  'nsfw-video':['short_porn','XxxHDVideos','porn','nsfw','HotNSFWvideo','nsfwvideos'],
};
const _reddvideoCache = new Map();
const _REDDVIDEO_CACHE_TTL = 20 * 60 * 1000;

// Fetch from reddvideo.tube category page. Video mp4s are served from media.reddit.tube CDN.
// Cycles through slugs with persisted index; caches each page 20 min.
// Returns { url, videoUrl, type:'mp4', title, sub, source:'reddvideo' } or null.
async function fetchReddvideoContent(cat, seenSet) {
  const slugs = REDDVIDEO_CAT_SLUGS[cat];
  if (!slugs || !slugs.length) return null;
  const rvKey = `reddvideo:${cat}`;
  const rvIdx = _nsfwSubIndex.get(rvKey) || 0;
  _nsfwSubIndex.set(rvKey, (rvIdx + 1) % slugs.length);
  const slug = slugs[rvIdx % slugs.length];
  // Bias towards page 1 (gets cached on first load; subsequent calls instant).
  const page = Math.random() < 0.6 ? 1 : (Math.floor(Math.random() * 4) + 2);
  const cacheKey = `${slug}:${page}`;
  const cached = _reddvideoCache.get(cacheKey);
  let videos;
  if (cached && Date.now() - cached.ts < _REDDVIDEO_CACHE_TTL) {
    videos = cached.videos;
  } else {
    videos = await new Promise(resolve => {
      const p = page === 1 ? `/category/${encodeURIComponent(slug)}` : `/category/${encodeURIComponent(slug)}/${page}`;
      const req = https.request({
        hostname: 'www.reddvideo.tube', path: p, method: 'GET',
        headers: {
          'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
          'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
          'Accept-Language': 'en-US,en;q=0.9',
        }
      }, res => {
        if (res.statusCode >= 400) { res.resume(); vlog(`[ReddVideo] HTTP ${res.statusCode} /category/${slug}/${page}`); return resolve([]); }
        let d = ''; res.on('data', c => d += c);
        res.on('end', () => {
          // Try CDN URLs directly first, then fall back to href hash extraction.
          const cdnHashes = [...d.matchAll(/https:\/\/media\.reddit\.tube\/mp4\/([a-fA-F0-9]+)\.mp4/g)].map(m => m[1].toLowerCase());
          const hrefHashes = [...d.matchAll(/href="\/video\/([a-fA-F0-9]{20,60})"/g)].map(m => m[1].toLowerCase());
          const hashDedup = new Set();
          const hashes = [...cdnHashes, ...hrefHashes].filter(h => { if (hashDedup.has(h)) return false; hashDedup.add(h); return true; });
          // Extract titles from alt attributes on thumbnail imgs.
          const alts = [...d.matchAll(/<img[^>]+alt="([^"]+)"/g)].map(m => m[1].trim()).filter(t => t);
          const found = hashes.map((h, i) => ({ hash: h, title: alts[i] || null }));
          vlog(`[ReddVideo] /category/${slug}/${page} parsed ${found.length} videos`);
          resolve(found);
        });
      });
      req.on('error', e => { vlog(`[ReddVideo] error: ${e.message}`); resolve([]); });
      req.setTimeout(12000, () => { req.destroy(); vlog('[ReddVideo] timeout'); resolve([]); });
      req.end();
    });
    if (videos.length) _reddvideoCache.set(cacheKey, { videos, ts: Date.now() });
  }
  if (!videos || !videos.length) return null;
  const available = seenSet
    ? videos.filter(v => !seenSet.has(v.hash) && !seenSet.has(`https://media.reddit.tube/mp4/${v.hash}.mp4?v=19700101120000`))
    : videos;
  const pool = available.length ? available : videos;
  const pick = pool[Math.floor(Math.random() * Math.min(pool.length, 20))];
  const videoUrl = `https://media.reddit.tube/mp4/${pick.hash}.mp4?v=19700101120000`;
  const pageUrl = `https://www.reddvideo.tube/video/${pick.hash}`;
  if (seenSet) { seenSet.add(pick.hash); seenSet.add(videoUrl); seenSet.add(pageUrl); }
  vlog(`[ReddVideo] cat="${cat}" slug="${slug}" page=${page} hash="${pick.hash}"`);
  return { url: pageUrl, videoUrl, type: 'mp4', title: pick.title || null, sub: slug, source: 'reddvideo' };
}

async function _getRedgifsToken() {
  if (_redgifsToken && Date.now() < _redgifsTokenExpiry) return _redgifsToken;
  const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36';
  try {
    _redgifsToken = await new Promise((resolve, reject) => {
      const req = https.get('https://api.redgifs.com/v2/auth/temporary',
        { headers: { 'User-Agent': UA, 'Accept': 'application/json' } },
        res => {
          let d = ''; res.on('data', c => d += c);
          res.on('end', () => { try { resolve(JSON.parse(d).token || ''); } catch { resolve(''); } });
        });
      req.on('error', reject);
      req.setTimeout(6000, () => { req.destroy(); reject(new Error('timeout')); });
    });
    _redgifsTokenExpiry = Date.now() + 23 * 60 * 60 * 1000;
    vlog(`[Redgifs] token acquired (${_redgifsToken.slice(0,12)}...)`);
  } catch (e) { vlog(`[Redgifs] token fetch failed: ${e.message}`); _redgifsToken = ''; }
  return _redgifsToken;
}

// Search Redgifs for NSFW video content. Returns { url, videoUrl, type:'mp4', title, sub:'redgifs' } or null.
// requiredTags: array of category tags — only gifs whose own tags include at least one are considered.
// No credentials required — uses a free temporary token that Redgifs issues to any client.
async function fetchRedgifsContent(query, seenSet, requiredTags) {
  if (Date.now() < _redgifsRateLimitUntil) { vlog(`[Redgifs] rate limited, skipping search for "${query}"`); return null; }
  const token = await _getRedgifsToken();
  if (!token) { vlog('[Redgifs] no token'); return null; }
  const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36';
  const q = encodeURIComponent(query);
  const orders = ['trending', 'top', 'top7', 'top28', 'score'];
  const order = orders[Math.floor(Math.random() * orders.length)];
  const page = Math.floor(Math.random() * 3) + 1;
  const url = `https://api.redgifs.com/v2/gifs/search?search_text=${q}&count=50&order=${order}&page=${page}`;
  return new Promise(resolve => {
    const req = https.get(url, {
      headers: { 'User-Agent': UA, 'Accept': 'application/json', 'Authorization': `Bearer ${token}` }
    }, res => {
      const status = res.statusCode;
      let d = ''; res.on('data', c => d += c);
      res.on('end', () => {
        if (status === 429) {
          try { const delay = JSON.parse(d).error?.delay || 120; _redgifsRateLimitUntil = Math.max(_redgifsRateLimitUntil, Date.now() + delay * 1000); } catch {}
        }
        if (status >= 400) { vlog(`[Redgifs search] ${status} body: ${d.slice(0, 200)}`); return resolve(null); }
        try {
          const parsed = JSON.parse(d);
          const gifs = parsed.gifs || [];
          vlog(`[Redgifs search] ${status} — ${gifs.length} results for "${query}" (order:${order} page:${page})`);
          const norm = s => s.toLowerCase().replace(/[\s\-_]/g, '');
          const normRequired = requiredTags ? requiredTags.map(norm) : null;
          let candidates = gifs.filter(g => g?.urls?.hd && g.hasAudio !== false && (!seenSet || !seenSet.has(g.urls.hd)));
          if (normRequired && candidates.length) {
            const tagged = candidates.filter(g => {
              const gifTags = (g.tags || []).map(norm);
              return normRequired.some(rt => gifTags.includes(rt));
            });
            vlog(`[Redgifs search] tag filter: ${tagged.length}/${candidates.length} match [${normRequired.join(',')}]`);
            if (!tagged.length) return resolve(null); // nothing on-category — caller retries with different query
            candidates = tagged;
          }
          if (!candidates.length) return resolve(null);
          const pick = candidates[Math.floor(Math.random() * Math.min(candidates.length, 30))];
          const hdUrl = pick.urls.hd.replace(/\.hd\.mp4(\?|$)/i, '.mp4$1');
          const watchUrl = `https://www.redgifs.com/watch/${pick.id}`;
          if (seenSet) seenSet.add(hdUrl);
          resolve({ url: watchUrl, videoUrl: hdUrl, type: 'redgif', title: (pick.tags || []).slice(0, 3).join(' ') || query, sub: 'redgifs' });
        } catch (e) { vlog(`[Redgifs search] parse error: ${e.message} body: ${d.slice(0, 200)}`); resolve(null); }
      });
    });
    req.on('error', e => { vlog(`[Redgifs search] network error: ${e.message}`); resolve(null); });
    req.setTimeout(10000, () => { req.destroy(); vlog('[Redgifs search] timeout'); resolve(null); });
  });
}

// Fetch content from a specific Redgifs niche category. More precise than search — content is pre-categorized by Redgifs.
// Valid niche sort orders: trending, oldest, latest, best, hot (NOT top/top7/top28/score — those are search-only)
async function fetchRedgifsNiche(niche, seenSet, requiredTags) {
  if (Date.now() < _redgifsRateLimitUntil) { vlog(`[Redgifs] rate limited, skipping niche "${niche}"`); return null; }
  // Serve from cache if fresh — avoids repeated API calls for the same niche
  const _cached = _redgifsNicheCache.get(niche);
  if (_cached && Date.now() - _cached.ts < _RGIFS_CACHE_TTL) {
    const candidates = _cached.gifs.filter(g => g?.urls?.hd && g.hasAudio !== false && (!seenSet || !seenSet.has(g.urls.hd)));
    if (candidates.length) {
      const pick = candidates[Math.floor(Math.random() * Math.min(candidates.length, 60))];
      const hdUrl = pick.urls.hd.replace(/\.hd\.mp4(\?|$)/i, '.mp4$1');
      if (seenSet) seenSet.add(hdUrl);
      vlog(`[Redgifs niche] cache hit "${niche}" — ${candidates.length} available`);
      return { url: `https://www.redgifs.com/watch/${pick.id}`, videoUrl: hdUrl, type: 'redgif', title: (pick.tags || []).slice(0, 3).join(' ') || niche, sub: 'redgifs' };
    }
    vlog(`[Redgifs niche] cache hit "${niche}" but all seen — skipping`);
    return null;
  }
  const token = await _getRedgifsToken();
  if (!token) { vlog('[Redgifs] no token'); return null; }
  const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36';
  const orders = ['trending', 'best', 'hot', 'latest', 'oldest'];
  const order = orders[Math.floor(Math.random() * orders.length)];
  const page = Math.floor(Math.random() * 3) + 1;
  const url = `https://api.redgifs.com/v2/niches/${encodeURIComponent(niche)}/gifs?count=80&order=${order}&page=${page}`;
  return new Promise(resolve => {
    const req = https.get(url, {
      headers: { 'User-Agent': UA, 'Accept': 'application/json', 'Authorization': `Bearer ${token}` }
    }, res => {
      const status = res.statusCode;
      let d = ''; res.on('data', c => d += c);
      res.on('end', () => {
        if (status === 429) {
          try { const delay = JSON.parse(d).error?.delay || 120; _redgifsRateLimitUntil = Math.max(_redgifsRateLimitUntil, Date.now() + delay * 1000); } catch {}
        }
        if (status === 301) {
          const loc = res.headers.location;
          if (!loc) { vlog(`[Redgifs niche] 301 no location for "${niche}"`); return resolve(null); }
          vlog(`[Redgifs niche] 301 redirect "${niche}" → ${loc}`);
          const rReq = https.get(loc, { headers: { 'User-Agent': UA, 'Accept': 'application/json', 'Authorization': `Bearer ${token}` } }, rRes => {
            const rStatus = rRes.statusCode;
            let rd = ''; rRes.on('data', c => rd += c);
            rRes.on('end', () => {
              if (rStatus >= 400) { vlog(`[Redgifs niche] redirect ${rStatus} for "${niche}"`); return resolve(null); }
              try {
                const parsed = JSON.parse(rd);
                const gifs = parsed.gifs || [];
                vlog(`[Redgifs niche] redirect ${rStatus} — ${gifs.length} results for "${niche}"`);
                if (gifs.length) _redgifsNicheCache.set(niche, { gifs, ts: Date.now() });
                const candidates = gifs.filter(g => g?.urls?.hd && (!seenSet || !seenSet.has(g.urls.hd)));
                if (!candidates.length) return resolve(null);
                const pick = candidates[Math.floor(Math.random() * Math.min(candidates.length, 60))];
                const hdUrl = pick.urls.hd.replace(/\.hd\.mp4(\?|$)/i, '.mp4$1');
                if (seenSet) seenSet.add(hdUrl);
                resolve({ url: `https://www.redgifs.com/watch/${pick.id}`, videoUrl: hdUrl, type: 'redgif', title: (pick.tags || []).slice(0, 3).join(' ') || niche, sub: 'redgifs' });
              } catch (e) { vlog(`[Redgifs niche] redirect parse error: ${e.message}`); resolve(null); }
            });
          });
          rReq.on('error', e => { vlog(`[Redgifs niche] redirect error: ${e.message}`); resolve(null); });
          rReq.setTimeout(10000, () => { rReq.destroy(); vlog('[Redgifs niche] redirect timeout'); resolve(null); });
          return;
        }
        if (status >= 400) { vlog(`[Redgifs niche] ${status} for "${niche}" body: ${d.slice(0, 200)}`); return resolve(null); }
        try {
          const parsed = JSON.parse(d);
          const gifs = parsed.gifs || [];
          vlog(`[Redgifs niche] ${status} — ${gifs.length} results for "${niche}" (order:${order} page:${page})`);
          if (gifs.length) {
            _redgifsNicheCache.set(niche, { gifs, ts: Date.now() });
            if (_redgifsNicheCache.size > 200) {
              const oldest = [..._redgifsNicheCache.entries()].sort(([,a],[,b]) => a.ts - b.ts)[0];
              _redgifsNicheCache.delete(oldest[0]);
            }
          }
          let candidates = gifs.filter(g => g?.urls?.hd && g.hasAudio !== false && (!seenSet || !seenSet.has(g.urls.hd)));
          if (!candidates.length) return resolve(null);
          const pick = candidates[Math.floor(Math.random() * Math.min(candidates.length, 60))];
          const hdUrl = pick.urls.hd.replace(/\.hd\.mp4(\?|$)/i, '.mp4$1');
          const watchUrl = `https://www.redgifs.com/watch/${pick.id}`;
          if (seenSet) seenSet.add(hdUrl);
          resolve({ url: watchUrl, videoUrl: hdUrl, type: 'redgif', title: (pick.tags || []).slice(0, 3).join(' ') || niche, sub: 'redgifs' });
        } catch (e) { vlog(`[Redgifs niche] parse error: ${e.message}`); resolve(null); }
      });
    });
    req.on('error', e => { vlog(`[Redgifs niche] network error: ${e.message}`); resolve(null); });
    req.setTimeout(10000, () => { req.destroy(); vlog('[Redgifs niche] timeout'); resolve(null); });
  });
}

// Returns the video URL as a single-element array — always HD, no quality downgrade.
const DISCORD_UPLOAD_MAX = 8 * 1024 * 1024; // 8 MB — bot file upload limit

// Permission bits for roles that should never be self-assignable by regular members
const ELEVATED_PERM_BITS = BigInt('0x8')        // ADMINISTRATOR
  | BigInt('0x4')        // BAN_MEMBERS
  | BigInt('0x2')        // KICK_MEMBERS
  | BigInt('0x20')       // MANAGE_GUILD
  | BigInt('0x10')       // MANAGE_CHANNELS
  | BigInt('0x10000000') // MANAGE_ROLES
  | BigInt('0x20000000') // MANAGE_WEBHOOKS
  | BigInt('0x400000000')// MODERATE_MEMBERS (timeout)
  | BigInt('0x2000')     // MANAGE_MESSAGES
  | BigInt('0x1000000'); // MOVE_MEMBERS
function _isElevatedRole(role) {
  try { return (BigInt(role.permissions) & ELEVATED_PERM_BITS) !== 0n; } catch { return false; }
}

function _videoUrlFallbacks(url) {
  if (/v\.redd\.it.*DASH_\d+\.mp4/i.test(url)) {
    const match = url.match(/DASH_(\d+)\.mp4/i);
    const current = match ? parseInt(match[1], 10) : 720;
    return [720, 480, 360, 240]
      .filter(q => q <= current)
      .map(q => url.replace(/DASH_\d+\.mp4/i, `DASH_${q}.mp4`));
  }
  // Redgifs HD → SD fallback: if HD is too large or fails, SD still has the same audio track
  if (/media\.redgifs\.com\/.+\.hd\.mp4/i.test(url)) {
    return [url, url.replace(/\.hd\.mp4(\?.*)?$/i, '.mp4')];
  }
  return [url];
}

function _typeMatchesFilter(type, typeFilter) {
  if (!typeFilter || typeFilter === 'any') return !!type;
  if (typeFilter === 'image') return type === 'image';
  if (typeFilter === 'gif') return type === 'gif';
  if (typeFilter === 'video') return type === 'mp4' || type === 'redgif';
  if (typeFilter === 'static') return type === 'image' || type === 'gif';
  return !!type;
}

// Extract the richest embeddable data from a Reddit post object.
// Returns { url, previewUrl, type, videoUrl, title, author } or null.
// - url / type:  what we use for type-filtering (the original media type)
// - previewUrl:  i.redd.it thumbnail — always use this as embed.image.url when present
// - videoUrl:    for mp4 posts, the actual playback link (shown as "▶ View" in embed)
function _resolveRedditPost(p) {
  let url = p.url || '';

  // Imgur .gifv is an HTML wrapper page — swap to .gif to get the direct animated image
  if (/\.gifv(\?|$)/i.test(url)) url = url.replace(/\.gifv(\?|$)/i, '.gif$1');

  let type = _classifyUrl(url);
  let previewUrl = null;
  let videoUrl = null;
  let galleryItems = null;

  // Reddit preview thumbnail (static JPEG — only use as last resort)
  const rawPreview = p.preview?.images?.[0]?.source?.url;
  if (rawPreview) previewUrl = rawPreview.replace(/&amp;/g, '&');

  // Reddit-hosted video: extract direct mp4 from media.reddit_video.fallback_url
  if (!type && p.media?.reddit_video?.fallback_url) {
    videoUrl = p.media.reddit_video.fallback_url.replace(/&amp;/g, '&');
    url = videoUrl;
    type = 'mp4';
  }

  // Gallery: extract ALL items (up to 10) so Discord shows the full image set
  if (!type && p.is_gallery && p.gallery_data?.items?.length) {
    const items = [];
    for (const item of p.gallery_data.items) {
      if (items.length >= 10) break;
      const mediaId = item.media_id;
      if (!mediaId || !p.media_metadata?.[mediaId]) continue;
      const meta = p.media_metadata[mediaId];
      if (meta.status !== 'valid') continue;
      const mime = meta.m || 'image/jpeg';
      const ext = mime.includes('gif') ? 'gif' : mime.includes('png') ? 'png' : 'jpg';
      const itemUrl = `https://i.redd.it/${mediaId}.${ext}`;
      items.push({ url: itemUrl, type: _classifyUrl(itemUrl) || 'image' });
    }
    if (items.length) {
      url = items[0].url;
      type = items[0].type;
      if (!previewUrl) previewUrl = url;
      if (items.length >= 2) galleryItems = items;
    }
  }

  // For redgif/mp4: videoUrl is the playback URL; previewUrl used as fallback thumbnail
  if ((type === 'mp4' || type === 'redgif') && !videoUrl) videoUrl = url;

  // Reddit stores an animated GIF variant in preview data for every GIF/animated post,
  // even when the main URL resolved to a static image type. Prefer this over the static JPEG.
  if (type === 'image' || !type) {
    const gifVariant = p.preview?.images?.[0]?.variants?.gif?.source?.url;
    if (gifVariant) {
      const gUrl = gifVariant.replace(/&amp;/g, '&');
      if (_classifyUrl(gUrl) === 'gif') { url = gUrl; type = 'gif'; }
    }
  }

  // Last-resort: use Reddit's static preview JPEG only when nothing animated resolved
  if (!type && previewUrl) {
    const t = _classifyUrl(previewUrl);
    if (t) { url = previewUrl; type = t; }
  }

  if (!type) return null;
  // Reddit DASH (v.redd.it) and redgifs both carry a separate audio track.
  // External .mp4 links (imgur etc.) are almost always silent.
  const hasLikelyAudio = type === 'redgif' || (type === 'mp4' && /v\.redd\.it/i.test(videoUrl || ''));
  return {
    url, previewUrl, videoUrl, type, hasLikelyAudio,
    title:   p.title       || null,
    author:  p.author      || null,
    score:   p.score       || 0,
    created: p.created_utc || null,
    galleryItems,
  };
}

// Returns true if the post appears to be male/gay-focused so it can be skipped.
// Trans content is intentionally allowed and must not match these patterns.
function _isMaleContent(title, sub) {
  const t = (title || '').toLowerCase();
  const s = (sub   || '').toLowerCase();
  // GWA-style performer tags embedded in Reddit post titles ([M4F],[M4M],[M4A] = male performer)
  if (/\[m4[mfa]\]/i.test(title)) return true;
  // Title-based signals for gay or male-solo content
  if (/\bgay\b|\bm4m\b|\btwinks?\b|\bbara\b|\byaoi\b|\bfemboy\b|\bfemboys\b/.test(t)) return true;
  if (/\bmale\s+(nude|solo|masturbat|orgasm|moaning|joi)\b/.test(t)) return true;
  if (/\bsolo\s+male\b|\bmale\s+solo\b/.test(t)) return true;
  if (/\b(man|men|guy)\s+(nude|solo|naked|moaning|masturbat)\b/.test(t)) return true;
  if (/\bgay\s+(porn|sex|anal|blowjob|cum|nude|cock)\b/.test(t)) return true;
  // Subreddit name patterns (check both prefix and full match for common gay sub names)
  if (/^gay|gaynsfw|gayporn|gaysfw|^m4m\b|twinkporn|malesfw|boysnsfw/.test(s)) return true;
  if (/gayboys|gaycocks|gaysex|gaynude|gaybros|gayssfw/.test(s)) return true;
  if (/^femboy|femboys|^twinks?_|twink_nsfw|crossdress|sissif/.test(s)) return true;
  return false;
}

// Returns true if an audio/ASMR title is male-performed and should be skipped.
// Covers GWA performer tags ([M4F],[M4M],[M4A]), explicit male-voice descriptors,
// and gay/m4m signals. [F4M],[F4F],[F4A] = female performer → allowed.
function _isMaleAudio(title) {
  const t = (title || '').toLowerCase();
  // GWA performer tags: [M4*] = male performer regardless of audience
  if (/\[m4[mfab]\]/i.test(title)) return true;
  if (/\b(gay|m4m)\b/.test(t)) return true;
  if (/\bmale\s+(audio|voice|asmr|dirty\s*talk|moaning|orgasm|joi|performer)\b/.test(t)) return true;
  if (/\b(guy|man|men|male)\s+(moaning|dirty\s*talk|asmr|orgasm|cumming|audio|voice)\b/.test(t)) return true;
  if (/\bboyfriend\s+asmr\b|\bbf\s+asmr\b|\bmale\s+joi\b/.test(t)) return true;
  if (/\bsolo\s+male\b|\bmale\s+solo\b|\bgay\s+asmr\b/.test(t)) return true;
  return false;
}

// Tries subs in parallel batches for speed — sequential is too slow with large sub lists.
// Uses RSS feeds which bypass Reddit's NSFW auth restriction on the JSON API.
async function fetchRedditNsfw(subs, typeFilter, seenSet) {
  const subList = Array.isArray(subs) ? [...subs] : [subs];
  subList.sort(() => Math.random() - 0.5);
  const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36';
  const opts = { headers: { 'User-Agent': UA, 'Accept': 'application/rss+xml, application/xml, */*' } };

  const tryOne = (sub, sort) => new Promise(resolve => {
    const suffix = sort === 'top' ? '?limit=100&t=month' : '?limit=100';
    const url = `https://www.reddit.com/r/${sub}/${sort}.rss${suffix}`;
    const hit = _redditRawCache.get(url);
    if (hit && Date.now() - hit.ts < _REDDIT_CACHE_TTL) return resolve(_pickRssPost(_parseRedditRss(hit.raw), typeFilter, seenSet));
    if (Date.now() < _redditBackoffUntil) return resolve(hit ? _pickRssPost(_parseRedditRss(hit.raw), typeFilter, seenSet) : null);
    const req = https.get(url, opts, res => {
      if (res.statusCode === 429 || res.statusCode === 503) {
        res.resume();
        _redditBackoffUntil = Date.now() + 90_000;
        return resolve(hit ? _pickRssPost(_parseRedditRss(hit.raw), typeFilter, seenSet) : null);
      }
      if (res.statusCode >= 400) {
        vlog(`[Reddit RSS] ${res.statusCode} for r/${sub} (${sort})`);
        res.resume(); return resolve(null);
      }
      if (res.statusCode >= 300 && res.headers.location) {
        const r2 = https.get(res.headers.location, opts, r => {
          let d = ''; r.on('data', c => d += c);
          r.on('end', () => { _redditRawCache.set(url, { raw: d, ts: Date.now() }); resolve(_pickRssPost(_parseRedditRss(d), typeFilter, seenSet)); });
        });
        r2.on('error', () => resolve(null)); r2.setTimeout(6000, () => { r2.destroy(); resolve(null); });
        return;
      }
      let d = ''; res.on('data', c => d += c);
      res.on('end', () => { _redditRawCache.set(url, { raw: d, ts: Date.now() }); resolve(_pickRssPost(_parseRedditRss(d), typeFilter, seenSet)); });
    });
    req.on('error', () => resolve(null)); req.setTimeout(8000, () => { req.destroy(); resolve(null); });
  });

  const BATCH = 6;
  for (const sort of ['hot', 'new', 'top']) {
    for (let i = 0; i < subList.length; i += BATCH) {
      const batch = subList.slice(i, i + BATCH);
      const result = await new Promise(resolve => {
        let remaining = batch.length;
        let done = false;
        for (const sub of batch) {
          tryOne(sub, sort).then(r => {
            if (r && !done) { done = true; resolve(r); }
            else if (--remaining === 0 && !done) resolve(null);
          });
        }
      });
      if (result) return result;
    }
  }
  return null;
}

// Reddit-wide NSFW search — fallback when specific subreddits are quarantined/empty.
// Uses RSS search which bypasses the NSFW auth restriction on the JSON API.
async function searchRedditNsfw(query, typeFilter, seenSet) {
  const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36';
  const opts = { headers: { 'User-Agent': UA, 'Accept': 'application/rss+xml, application/xml, */*' } };
  const q = encodeURIComponent(query);
  const endpoints = [
    `https://www.reddit.com/search.rss?q=${q}&sort=hot&type=link&nsfw=1&limit=50`,
    `https://www.reddit.com/search.rss?q=${q}&sort=top&type=link&nsfw=1&limit=50&t=month`,
  ];
  for (const endpoint of endpoints) {
    const result = await new Promise(resolve => {
      const hit = _redditRawCache.get(endpoint);
      if (hit && Date.now() - hit.ts < _REDDIT_CACHE_TTL) return resolve(_pickRssPost(_parseRedditRss(hit.raw), typeFilter, seenSet));
      if (Date.now() < _redditBackoffUntil) return resolve(hit ? _pickRssPost(_parseRedditRss(hit.raw), typeFilter, seenSet) : null);
      const req = https.get(endpoint, opts, res => {
        if (res.statusCode === 429 || res.statusCode === 503) {
          res.resume();
          _redditBackoffUntil = Date.now() + 90_000;
          return resolve(hit ? _pickRssPost(_parseRedditRss(hit.raw), typeFilter, seenSet) : null);
        }
        if (res.statusCode >= 400) {
          vlog(`[Reddit RSS search] ${res.statusCode} for: ${query}`);
          res.resume(); return resolve(null);
        }
        let d = ''; res.on('data', c => d += c);
        res.on('end', () => {
          _redditRawCache.set(endpoint, { raw: d, ts: Date.now() });
          resolve(_pickRssPost(_parseRedditRss(d), typeFilter, seenSet));
        });
      });
      req.on('error', () => resolve(null)); req.setTimeout(7000, () => { req.destroy(); resolve(null); });
    });
    if (result) return result;
  }
  return null;
}



// Fetches a random hentai image from e621 (tag-based booru). Returns { url, postUrl, tags } or null.
async function fetchE621(tags) {
  const tagStr = encodeURIComponent((tags || 'animated explicit -scat -gore -guro').split(' ').join('+'));
  const page = Math.floor(Math.random() * 50) + 1;
  const url = `https://e621.net/posts.json?tags=${tagStr}&limit=40&page=${page}`;
  return new Promise(resolve => {
    const req = https.get(url, {
      headers: {
        'User-Agent': 'DiscordBot/1.0 (by anonymous)',
        'Accept': 'application/json',
      }
    }, res => {
      let d = ''; res.on('data', c => d += c);
      res.on('end', () => {
        try {
          const posts = JSON.parse(d).posts || [];
          const valid = posts.filter(p =>
            p.file?.url && /\.(jpg|jpeg|png|gif|webm|mp4)$/i.test(p.file.url) &&
            p.rating === 'e' && !p.flags?.deleted
          );
          if (!valid.length) return resolve(null);
          const pick = valid[Math.floor(Math.random() * valid.length)];
          resolve({ url: pick.file.url, postUrl: `https://e621.net/posts/${pick.id}`, tags: pick.tags?.general || [] });
        } catch { resolve(null); }
      });
    });
    req.on('error', () => resolve(null));
    req.setTimeout(8000, () => { req.destroy(); resolve(null); });
  });
}

// ── Groq sext AI call — supports optional imageUrl for vision reactions (e.g. dick pics) ──
function groqSext(messages, systemPrompt, imageUrl) {
  return new Promise((resolve, reject) => {
    const processed = messages.slice(-12).map((m, i, arr) => {
      if (i === arr.length - 1 && m.role === 'user' && imageUrl) {
        return {
          role: 'user',
          content: [
            { type: 'image_url', image_url: { url: imageUrl } },
            { type: 'text', text: m.content || 'React to what I just sent you.' },
          ],
        };
      }
      return m;
    });
    const body = JSON.stringify({
      model: 'meta-llama/llama-4-scout-17b-16e-instruct',
      max_tokens: 250,
      messages: [{ role: 'system', content: systemPrompt }, ...processed],
    });
    const req = https.request({
      hostname: 'api.groq.com',
      path: '/openai/v1/chat/completions',
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${process.env.GROQ_API_KEY}`,
        'Content-Type': 'application/json',
        'Content-Length': Buffer.byteLength(body),
      },
    }, res => {
      let raw = '';
      res.on('data', c => raw += c);
      res.on('end', () => {
        try { resolve(JSON.parse(raw).choices?.[0]?.message?.content || ''); }
        catch { reject(new Error('parse')); }
      });
    });
    req.on('error', reject);
    req.setTimeout(15000, () => { req.destroy(); reject(new Error('timeout')); });
    req.write(body);
    req.end();
  });
}

// Searches PornHub + YouTube for ASMR audio — type can be 'moan','wetpussy','dirtytalk','whisper','breathing'
function fetchAsmrClip(personaQuery, asmrType) {
  const outPath = path.join(process.env.KP_APP_TMP || require('os').tmpdir(), `asmr_${Date.now()}.mp3`);
  const q = personaQuery || 'girlfriend';
  const _aph = s => `https://www.pornhub.com/video/search?search=${encodeURIComponent(s)}`;
  const TYPE_SOURCES = {
    moan:      [_aph(`female moaning orgasm audio ${q}`), _aph(`female orgasm moan audio`), `ytsearch3:moaning sounds erotic female`],
    wetpussy:  [_aph(`wet pussy sounds ${q}`), _aph(`wet sounds pussy close up female`), `ytsearch3:wet pussy asmr sounds female`],
    dirtytalk: [_aph(`dirty talk female ${q}`), _aph(`dirty talk female audio girlfriend`), `ytsearch3:dirty talk asmr female ${q} girlfriend`],
    whisper:   [`ytsearch3:asmr whisper girlfriend roleplay ${q}`, _aph(`asmr whisper female ${q}`), `ytsearch3:ear asmr whisper erotic female`],
    breathing: [`ytsearch3:asmr heavy breathing female ${q}`, _aph(`asmr breathing erotic female`), `ytsearch3:erotic breathing asmr girlfriend female`],
  };
  const sources = TYPE_SOURCES[asmrType] || [
    _aph(`asmr erotic audio female ${q}`),
    _aph(`dirty talk moaning female ${q}`),
    `ytsearch3:asmr girlfriend roleplay ${q} audio female`,
  ];
  return (async () => {
    for (const src of sources) {
      const videoUrl = await new Promise(res => {
        execFile(getBin('yt-dlp'), [
          src, '--flat-playlist', '--playlist-end', '5',
          '--print', '%(url)s',
          '--no-warnings', '--quiet',
          '--add-header', 'Cookie:il=1; platform=pc',
        ], { timeout: 12000, env: _kpEnv() }, (err, stdout) => {
          const lines = (stdout || '').trim().split('\n').filter(l => l && l.length > 5);
          res(lines[Math.floor(Math.random() * Math.min(lines.length, 3))] || null);
        });
      });
      if (!videoUrl) continue;
      const ok = await new Promise(res => {
        execFile(getBin('yt-dlp'), [
          videoUrl,
          '--download-sections', '*0:30-1:00',
          '-x', '--audio-format', 'mp3', '--audio-quality', '5',
          '--ffmpeg-location', path.dirname(getBin('ffmpeg')),
          '--output', outPath,
          '--no-playlist', '--no-warnings', '--quiet',
          '--add-header', 'Cookie:il=1; platform=pc',
        ], { timeout: 45000, env: _kpEnv() }, (err) => res(!err));
      });
      if (!ok) continue;
      try {
        const buf = fs.readFileSync(outPath);
        try { fs.unlinkSync(outPath); } catch {}
        if (buf.length > 500 && buf.length < 8 * 1024 * 1024) return buf;
      } catch {}
    }
    return null;
  })();
}

const _eroFeedCache = new Map(); // term -> { items, ts }
const EROASMR_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36';

// Fetches eroasmr.com RSS feed items for a search term. Results are cached for 10 minutes.
async function fetchEroAsmrFeed(term) {
  const key = (term || 'dirty talk asmr').toLowerCase().trim();
  const cached = _eroFeedCache.get(key);
  if (cached && Date.now() - cached.ts < 10 * 60 * 1000) return cached.items;
  const q = key.replace(/\s+/g, '+');
  const xml = await new Promise(resolve => {
    const req = https.get(`https://eroasmr.com/search/${q}/feed/rss2/`,
      { headers: { 'User-Agent': EROASMR_UA } }, res => {
        if (res.statusCode >= 400) { res.resume(); return resolve(''); }
        let d = ''; res.on('data', c => d += c); res.on('end', () => resolve(d));
      });
    req.on('error', () => resolve(''));
    req.setTimeout(10000, () => { req.destroy(); resolve(''); });
  });
  const items = [];
  for (const m of (xml || '').matchAll(/<item>([\s\S]*?)<\/item>/g)) {
    const x = m[1];
    const link  = (x.match(/<link>(https:\/\/eroasmr\.com\/video\/[^<]+)<\/link>/) || [])[1];
    const title = (x.match(/<title>(?:<!\[CDATA\[)?([^\]<]+?)(?:\]\]>)?<\/title>/) || [])[1]?.trim();
    if (link) items.push({ pageUrl: link, title: title || 'EroASMR Audio' });
  }
  _eroFeedCache.set(key, { items, ts: Date.now() });
  return items;
}

// Fetches one eroasmr post page and returns its direct MP4 URL, or null if not found.
function resolveEroAsmrMp4(pageUrl) {
  return new Promise(resolve => {
    const req = https.get(pageUrl, { headers: { 'User-Agent': EROASMR_UA } }, res => {
      if (res.statusCode >= 400) { res.resume(); return resolve(null); }
      let d = ''; res.on('data', c => d += c);
      res.on('end', () => {
        const m = d.match(/["'](https?:\/\/video\d*\.eroasmr\.com\/[^"'<>\s]+\.mp4)/i);
        resolve(m ? m[1] : null);
      });
    });
    req.on('error', () => resolve(null));
    req.setTimeout(6000, () => { req.destroy(); resolve(null); });
  });
}

// Extracts soundgasm URLs from a Reddit post's url field or selftext body.
function _extractSgLinks(post) {
  const links = [];
  const seen = new Set();
  const add = url => {
    const clean = url.replace(/[\)\]"'\s]+$/, '');
    if (!seen.has(clean) && /soundgasm\.net\/u\//i.test(clean)) { seen.add(clean); links.push(clean); }
  };
  if (/soundgasm\.net\/u\//i.test(post.url || '')) add(post.url);
  const text = post.selftext || post.selftext_html || '';
  for (const m of text.matchAll(/https?:\/\/soundgasm\.net\/u\/[^\s\)\]"']+/gi)) add(m[0]);
  return links;
}

// Searches Reddit GWA subs for audio posts and returns [{url,title}] of streamable soundgasm links.
async function fetchSoundgasmResults(term, limit = 20) {
  return fetchGonewildAudio(term, limit, 'search');
}

// Fetches audio posts from r/gonewildaudio and sibling subs — returns [{url,title}] of soundgasm links.
// Uses RSS feeds which bypass Reddit's NSFW auth restriction on the JSON API.
async function fetchGonewildAudio(term, limit = 20, mode = 'browse') {
  const GWA_SUBS = ['gonewildaudio', 'AudioSmut', 'WetAudio', 'GWASeries', 'gonewildaudiolibrary'];
  const UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36';
  const opts = { headers: { 'User-Agent': UA, 'Accept': 'application/rss+xml, application/xml, */*' } };
  const results = [];
  const seen = new Set();
  const termLc = (term || '').toLowerCase();

  const addFromItem = item => {
    if (_isMaleAudio(item.title)) return;
    // Link posts pointing directly to soundgasm
    if (/soundgasm\.net\/u\//i.test(item.link)) {
      const clean = item.link.replace(/[\)\]"'\s]+$/, '');
      if (!seen.has(clean)) { seen.add(clean); results.push({ url: clean, title: item.title || 'GWA Audio' }); }
    }
    // Soundgasm links embedded in self-post content
    for (const mx of (item.content || '').matchAll(/https?:\/\/soundgasm\.net\/u\/[^\s\)<>"'&]+/gi)) {
      const clean = mx[0].replace(/[\)\]"'\s&;]+$/, '');
      if (!seen.has(clean)) { seen.add(clean); results.push({ url: clean, title: item.title || 'GWA Audio' }); }
    }
  };

  const fetchRss = url => new Promise(resolve => {
    const hit = _redditRawCache.get(url);
    if (hit && Date.now() - hit.ts < _REDDIT_CACHE_TTL) return resolve(_parseRedditRss(hit.raw));
    const req = https.get(url, opts, res => {
      if (res.statusCode >= 400) { res.resume(); return resolve([]); }
      let d = ''; res.on('data', c => d += c);
      res.on('end', () => { _redditRawCache.set(url, { raw: d, ts: Date.now() }); resolve(_parseRedditRss(d)); });
    });
    req.on('error', () => resolve([]));
    req.setTimeout(8000, () => { req.destroy(); resolve([]); });
  });

  if (mode === 'search' && term) {
    const q = encodeURIComponent(term);
    for (const sub of GWA_SUBS) {
      const items = await fetchRss(`https://www.reddit.com/r/${sub}/search.rss?q=${q}&restrict_sr=1&limit=50&sort=relevance`);
      items.forEach(addFromItem);
      if (results.length >= limit) break;
    }
  } else {
    for (const sub of GWA_SUBS) {
      for (const sort of ['hot', 'new', 'top']) {
        const suffix = sort === 'top' ? '?limit=100&t=month' : '?limit=100';
        const items = await fetchRss(`https://www.reddit.com/r/${sub}/${sort}.rss${suffix}`);
        items.filter(i => !termLc || i.title.toLowerCase().includes(termLc)).forEach(addFromItem);
        if (results.length >= limit) break;
      }
      if (results.length >= limit) break;
    }
  }
  return results.slice(0, limit);
}


// Maps sext message text to a context-accurate POV visual search query and tags.
function pickSextVisualQuery(text, girlBase) {
  const t = (text || '').toLowerCase();
  const base = girlBase || 'pov nude amateur';
  if (/glid(e|ing)|rub(bing)?.*(pussy|lips)|grind(ing)?|hump/i.test(t))
    return { q: `pov pussy lips rubbing cock grinding ${base}`, tags: ['pov', 'grinding', 'rubbing', 'pussy'] };
  if (/rid(e|ing)|cowgirl|on top|bounc(e|ing)|sit(ting)? on (my|your) (cock|dick)/i.test(t))
    return { q: `pov riding cowgirl bouncing ${base}`, tags: ['pov', 'riding', 'cowgirl'] };
  if (/doggy|from behind|bent over|ass up|hit it from/i.test(t))
    return { q: `pov doggy style from behind ${base}`, tags: ['pov', 'doggy'] };
  if (/missionary|lay(ing)? down|spread.*legs|legs.*open|on (my|your) back/i.test(t))
    return { q: `pov missionary spread legs ${base}`, tags: ['pov', 'missionary'] };
  if (/blow(job)?|suck(ing)? (my )?(cock|dick)|on (her )?knees|throat|deepthroat/i.test(t))
    return { q: `pov blowjob eye contact deepthroat ${base}`, tags: ['pov', 'blowjob', 'deepthroat'] };
  if (/anal|in (my|your) ass|butt/i.test(t))
    return { q: `pov anal from behind ${base}`, tags: ['pov', 'anal'] };
  if (/cum(ming)?|creampie|finish|explode|bust|drench/i.test(t))
    return { q: `pov creampie cumshot ${base}`, tags: ['pov', 'creampie'] };
  if (/finger(ing)?|play(ing)? with.*(pussy|clit)|touch(ing)?.*(pussy|clit)/i.test(t))
    return { q: `pov fingering close up wet ${base}`, tags: ['pov', 'fingering', 'close-up'] };
  if (/strip|undress|tak(e|ing) off|clothes off/i.test(t))
    return { q: `pov striptease undressing tease solo ${base}`, tags: ['striptease', 'pov', 'solo'] };
  if (/bath|shower|wet body|drip/i.test(t))
    return { q: `pov nude shower wet ${base}`, tags: ['pov', 'shower', 'wet'] };
  if (/linger(ie)?|bra|panties|thong|lace/i.test(t))
    return { q: `lingerie pov strip tease ${base}`, tags: ['lingerie', 'pov', 'tease'] };
  if (/orgasm|climax|cum so hard|shaking/i.test(t))
    return { q: `pov orgasm moaning shaking ${base}`, tags: ['pov', 'orgasm'] };
  if (/kiss|lips|tongue|mouth/i.test(t))
    return { q: `pov kissing close up ${base}`, tags: ['pov', 'kissing', 'close-up'] };
  if (/ass|butt|booty|cheeks/i.test(t))
    return { q: `pov ass booty clapping ${base}`, tags: ['pov', 'ass'] };
  if (/breast|boob|tit|nipple/i.test(t))
    return { q: `pov breasts topless bouncing ${base}`, tags: ['pov', 'breasts', 'topless'] };
  if (/pussy|vagina|dripping wet|soaked/i.test(t))
    return { q: `pov pussy close up wet dripping ${base}`, tags: ['pov', 'pussy', 'close-up'] };
  return { q: `pov nude ${base}`, tags: ['pov', 'nude'] };
}

// Detects what type of audio the user is requesting.
function detectAsmrType(text) {
  const t = (text || '').toLowerCase();
  if (/moan(ing)?|orgasm|cum(ming)?|climax/.test(t)) return 'moan';
  if (/wet|squelch|pussy sound|drip|juicy/.test(t)) return 'wetpussy';
  if (/dirty talk|talk (to me|dirty)|say my name|beg/.test(t)) return 'dirtytalk';
  if (/whisper|breath(e|ing)?|asmr/.test(t)) return 'whisper';
  return 'moan';
}

function fetchTenorGif(query) {
  return new Promise(resolve => {
    const url = `https://api.tenor.com/v1/search?q=${encodeURIComponent(query)}&key=LIVDSRZULELA&limit=8&media_filter=minimal&contentfilter=low`;
    https.get(url, res => {
      let raw = '';
      res.on('data', d => raw += d);
      res.on('end', () => {
        try {
          const data = JSON.parse(raw);
          const results = data.results || [];
          if (!results.length) return resolve(null);
          const pick = results[Math.floor(Math.random() * Math.min(results.length, 8))];
          const m = pick.media?.[0] || {};
          resolve((m.gif || m.mediumgif || m.tinygif || {}).url || null);
        } catch { resolve(null); }
      });
    }).on('error', () => resolve(null));
  });
}

// Pipe yt-dlp -> ffmpeg so we always emit s16le 48kHz stereo PCM.
// Discord voice expects 48kHz; if we hand discord.js a raw bestaudio stream at
// 44.1k/22.05k/24k it can play back at the wrong speed (sounds sped-up/slowed).
// Resampling here makes playback rock-solid regardless of source sample rate.
// Pin TEMP/TMP for yt-dlp/ffmpeg to the app's scoped temp dir, and track pids
// so `before-quit` can SIGKILL them before wiping the dir.
function _kpEnv() { return (global.__kpEnv ? global.__kpEnv() : process.env); }
function _kpTrack(p) { return global.__kpTrack ? global.__kpTrack(p) : p; }
function createYtdlpStream(videoId) {
  const url = `https://www.youtube.com/watch?v=${videoId}`;
  const yt = _kpTrack(spawn(getBin('yt-dlp'), [
    url,
    '-f', 'bestaudio',
    '-o', '-',
    '--no-playlist', '--no-warnings', '--quiet',
    '--concurrent-fragments', '3',
  ], { stdio: ['ignore', 'pipe', 'pipe'], env: _kpEnv() }));
  const ff = _kpTrack(spawn(getBin('ffmpeg'), [
    '-hide_banner', '-loglevel', 'error',
    '-i', 'pipe:0',
    '-vn',
    '-f', 's16le',
    '-ar', '48000',
    '-ac', '2',
    'pipe:1'
  ], { stdio: ['pipe', 'pipe', 'pipe'], env: _kpEnv() }));
  yt.stdout.on('error', () => {});
  ff.stdin.on('error', () => {});
  yt.stdout.pipe(ff.stdin);
  yt.on('error', (e) => { try { ff.stdin.end(); } catch {} });
  ff.on('exit', () => { try { yt.kill('SIGKILL'); } catch {} });
  const origKill = ff.kill.bind(ff);
  ff.kill = (sig) => { try { yt.kill(sig || 'SIGKILL'); } catch {} return origKill(sig); };
  // Buffer ffmpeg output so small download hiccups don't starve the audio player.
  const buf = new PassThrough({ highWaterMark: 1024 * 1024 });
  ff.stdout.on('error', () => {});
  ff.stdout.pipe(buf);
  ff.stdout = buf;
  return ff;
}

function createFileStream(filePath) {
  const args = [
    '-hide_banner', '-loglevel', 'error',
    '-i', filePath,
    '-vn',
    '-f', 's16le',
    '-ar', '48000',
    '-ac', '2',
    'pipe:1'
  ];
  return _kpTrack(spawn(getBin('ffmpeg'), args, { stdio: ['ignore', 'pipe', 'pipe'], env: _kpEnv() }));
}

function _buildFilterStr(filters) {
  if (!filters) return null;
  const parts = [];
  if (filters.chipmunk)   parts.push('asetrate=48000*1.25,aresample=48000');
  if (filters.vaporwave)  parts.push('asetrate=48000*0.8,aresample=48000');
  if (filters.slowed)     parts.push('asetrate=48000*0.8,aresample=48000,atempo=0.9');
  if (filters['8d'])      parts.push('apulsator=hz=0.08');
  if (filters.reverb)     parts.push('aecho=0.8:0.9:1000:0.3');
  if (filters.earrape)    parts.push('volume=12,acrusher=level_in=1:level_out=12:bits=8:mode=log:aa=1');
  if (filters.bassboost) {
    const gain = filters.bassboost === 'low' ? 5 : filters.bassboost === 'high' ? 20 : 10;
    parts.push(`bass=g=${gain}`);
  }
  return parts.length ? parts.join(',') : null;
}
function _getPlaybackPos(state) {
  if (!state.trackStartedAt) return 0;
  const elapsed = Math.max(0, Math.floor((Date.now() - state.trackStartedAt) / 1000));
  return elapsed + (state.trackSeekBase || 0);
}

function createYtdlpStreamEx(videoId, seekSecs, filterStr) {
  const url = `https://www.youtube.com/watch?v=${videoId}`;
  const yt = _kpTrack(spawn(getBin('yt-dlp'), [
    url, '-f', 'bestaudio', '-o', '-', '--no-playlist', '--no-warnings', '--quiet',
    '--concurrent-fragments', '3',
  ], { stdio: ['ignore', 'pipe', 'pipe'], env: _kpEnv() }));
  const ffArgs = ['-hide_banner', '-loglevel', 'error', '-i', 'pipe:0'];
  if (seekSecs > 0) ffArgs.push('-ss', String(Math.floor(seekSecs)));
  ffArgs.push('-vn');
  if (filterStr) ffArgs.push('-af', filterStr);
  ffArgs.push('-f', 's16le', '-ar', '48000', '-ac', '2', 'pipe:1');
  const ff = _kpTrack(spawn(getBin('ffmpeg'), ffArgs, { stdio: ['pipe', 'pipe', 'pipe'], env: _kpEnv() }));
  yt.stdout.on('error', () => {}); ff.stdin.on('error', () => {});
  yt.stdout.pipe(ff.stdin);
  yt.on('error', () => { try { ff.stdin.end(); } catch {} });
  ff.on('exit', () => { try { yt.kill('SIGKILL'); } catch {} });
  const origKill = ff.kill.bind(ff);
  ff.kill = (sig) => { try { yt.kill(sig || 'SIGKILL'); } catch {} return origKill(sig); };
  // Buffer ffmpeg output so small download hiccups don't starve the audio player.
  const buf = new PassThrough({ highWaterMark: 1024 * 1024 });
  ff.stdout.on('error', () => {});
  ff.stdout.pipe(buf);
  ff.stdout = buf;
  return ff;
}
function createFileStreamEx(filePath, seekSecs, filterStr) {
  const ffArgs = ['-hide_banner', '-loglevel', 'error'];
  if (seekSecs > 0) ffArgs.push('-ss', String(Math.floor(seekSecs)));
  ffArgs.push('-i', filePath, '-vn');
  if (filterStr) ffArgs.push('-af', filterStr);
  ffArgs.push('-f', 's16le', '-ar', '48000', '-ac', '2', 'pipe:1');
  return _kpTrack(spawn(getBin('ffmpeg'), ffArgs, { stdio: ['ignore', 'pipe', 'pipe'], env: _kpEnv() }));
}
function _ytNorm(s) { return (s || '').toLowerCase().replace(/[^a-z0-9 ]+/g, ' ').replace(/\s+/g, ' ').trim(); }

function _scoreYtCandidate(c, expectedTitle, expectedArtist) {
  const up = _ytNorm(c.uploader);
  const ti = _ytNorm(c.title);
  const wantA = _ytNorm(expectedArtist);
  const wantT = _ytNorm(expectedTitle);
  let score = 0;
  // Auto-generated artist channels ("ArtistName - Topic") are by far the best signal.
  if (wantA && up.endsWith(' topic') && up.includes(wantA)) score += 100;
  else if (wantA && up.includes(wantA + ' vevo')) score += 60;
  else if (wantA && up.includes(wantA)) score += 40;
  if (wantT && ti.includes(wantT)) score += 25;
  // Penalize covers/remixes/live unless the user asked for them.
  if (/\b(cover|remix|live|sped up|slowed|nightcore|reverb|8d|karaoke|instrumental)\b/.test(ti) &&
      !/\b(cover|remix|live|sped up|slowed|nightcore|reverb|8d|karaoke|instrumental)\b/.test(_ytNorm(`${expectedTitle} ${expectedArtist}`))) {
    score -= 35;
  }
  // Prefer explicit cuts; penalize clean / radio edits unless user asked for them.
  const wantClean = /\b(clean|radio edit|radio version)\b/.test(_ytNorm(`${expectedTitle} ${expectedArtist}`));
  if (!wantClean && /\b(clean|clean version|radio edit|radio version|censored)\b/.test(ti)) {
    score -= 50;
  }
  if (/\b(explicit|dirty|uncensored|uncut)\b/.test(ti)) {
    score += 15;
  }
  return score;
}

function resolveYtSearch(query, expectedTitle, expectedArtist, expectedDurationMs) {
  return new Promise((resolve, reject) => {
    const SEP = '<<|>>';
    _kpTrack(execFile(getBin('yt-dlp'), [
      `ytsearch5:${query}`,
      '--print', `%(id)s${SEP}%(title)s${SEP}%(uploader)s${SEP}%(duration)s`,
      '--no-warnings', '--quiet', '--no-playlist',
      '--match-filter', '!is_live'
    ], { timeout: 25000, env: _kpEnv() }, (err, stdout, stderr) => {
      if (err) return reject(new Error((stderr || '').trim() || err.message));
      const lines = stdout.trim().split('\n').map(l => l.trim()).filter(Boolean);
      if (!lines.length) return reject(new Error('No results found'));
      const cands = lines.map(line => {
        const [id, title, uploader, duration] = line.split(SEP);
        return { videoId: (id || '').trim(), title: (title || '').trim(), uploader: (uploader || '').trim(), duration: parseInt(duration, 10) || 0 };
      }).filter(c => /^[a-zA-Z0-9_-]{11}$/.test(c.videoId));
      if (!cands.length) return reject(new Error('Could not parse result'));
      let pick = cands[0];
      if (expectedArtist || expectedTitle) {
        const expectedDurSecs = expectedDurationMs ? expectedDurationMs / 1000 : 0;
        const ranked = cands.map(c => {
          let s = _scoreYtCandidate(c, expectedTitle || '', expectedArtist || '');
          // Penalize candidates whose duration differs from the Spotify track by more than 15%.
          if (expectedDurSecs > 0 && c.duration > 0) {
            const diff = Math.abs(c.duration - expectedDurSecs) / expectedDurSecs;
            if (diff > 0.15) s -= 40;
          }
          return { c, s };
        }).sort((a, b) => b.s - a.s);
        pick = ranked[0].c;
      }
      resolve({ videoId: pick.videoId, title: pick.title || query, artist: pick.uploader || '', candidates: cands });
    }));
  });
}

// Module-level Spotify token cache (shared by resolveSpotifyTrack; the deployBot
// closure has its own independent cache for album-art lookups — both are fine).
const _SP_CLIENT_ID = 'e8ab66a616b54d97882d90864fbe2fb5';
const _SP_CLIENT_SECRET = '1dca3d2bce0743ef93112382e8936c30';
let _spToken = null, _spTokenExp = 0;
function _getSpToken() {
  return new Promise((resolve, reject) => {
    if (_spToken && Date.now() < _spTokenExp - 30_000) return resolve(_spToken);
    const body = 'grant_type=client_credentials';
    const auth = Buffer.from(`${_SP_CLIENT_ID}:${_SP_CLIENT_SECRET}`).toString('base64');
    const req = https.request({
      hostname: 'accounts.spotify.com', path: '/api/token', method: 'POST',
      headers: { Authorization: `Basic ${auth}`, 'Content-Type': 'application/x-www-form-urlencoded', 'Content-Length': Buffer.byteLength(body) },
    }, (res) => {
      let raw = ''; res.on('data', c => raw += c);
      res.on('end', () => {
        try {
          const d = JSON.parse(raw);
          if (!d.access_token) return reject(new Error('No Spotify token'));
          _spToken = d.access_token;
          _spTokenExp = Date.now() + (d.expires_in || 3600) * 1000;
          resolve(_spToken);
        } catch (e) { reject(e); }
      });
    });
    req.on('error', reject); req.end(body);
  });
}

function resolveSpotifyTrack(url) {
  return new Promise((resolve, reject) => {
    const m = url.match(/open\.spotify\.com\/(?:intl-\w+\/)?track\/([a-zA-Z0-9]+)/);
    if (!m) return reject(new Error('Not a Spotify track URL'));
    const id = m[1];
    _getSpToken().then(tok => {
      const req = https.get({
        hostname: 'api.spotify.com', path: `/v1/tracks/${id}`,
        headers: { Authorization: `Bearer ${tok}`, 'User-Agent': 'Mozilla/5.0' },
      }, (res) => {
        let raw = ''; res.on('data', c => raw += c);
        res.on('end', () => {
          try {
            const d = JSON.parse(raw);
            const title = d.name;
            const artist = (d.artists || [])[0]?.name || '';
            const durationMs = d.duration_ms || 0;
            if (!title) return reject(new Error('Spotify API returned no track name'));
            resolve({ title, artist, durationMs });
          } catch (e) { reject(e); }
        });
      });
      req.on('error', reject);
      req.setTimeout(10000, () => { req.destroy(new Error('Spotify API timed out')); });
    }).catch(reject);
  });
}

function parseLrcLines(lrc) {
  if (!lrc) return [];
  const out = [];
  for (const line of lrc.split('\n')) {
    const m = line.match(/^\[(\d+):(\d+(?:\.\d+)?)\](.*)$/);
    if (!m) continue;
    const t = parseInt(m[1], 10) * 60 + parseFloat(m[2]);
    const text = m[3].trim();
    if (text) out.push({ t, text });
  }
  return out.sort((a, b) => a.t - b.t);
}

function _cleanLyricTitle(title) {
  if (!title) return '';
  let t = title;
  t = t.replace(/\[[^\]]*\]/g, ' ');
  t = t.replace(/\([^)]*(official|video|audio|lyric|music|hd|hq|mv|visualizer|live|remix|version|explicit|clean|extended|edit)[^)]*\)/gi, ' ');
  t = t.replace(/\b(official\s+(music\s+)?(video|audio|lyric video|lyrics))\b/gi, ' ');
  t = t.replace(/\bft\.?\b|\bfeat\.?\b/gi, ' ');
  t = t.replace(/\s+/g, ' ').trim();
  t = t.replace(/[\-–—:|]+\s*$/, '').trim();
  return t;
}

function _cleanLyricArtist(artist) {
  if (!artist) return '';
  let a = artist.replace(/\bVEVO\b/gi, '').replace(/\s*-\s*Topic\s*$/i, '').replace(/\bOfficial\b/gi, '');
  a = a.replace(/\s+/g, ' ').trim();
  return a;
}

function _splitTitleArtist(title) {
  // Common YouTube title format: "Artist - Song" or "Song - Artist"
  const m = title.match(/^(.+?)\s+[\-–—]\s+(.+)$/);
  if (!m) return null;
  return { left: m[1].trim(), right: m[2].trim() };
}

function _lrclibGet(track, artist) {
  return new Promise((resolve) => {
    const params = new URLSearchParams({ track_name: track, artist_name: artist || '' });
    const req = https.get(`https://lrclib.net/api/get?${params}`, { headers: { 'User-Agent': 'DiscordBot/1.0' } }, (res) => {
      let raw = '';
      res.on('data', c => raw += c);
      res.on('end', () => {
        try {
          const d = JSON.parse(raw);
          if (d && (d.syncedLyrics || d.plainLyrics)) {
            resolve({ synced: d.syncedLyrics || null, plain: d.plainLyrics || null });
          } else resolve(null);
        } catch { resolve(null); }
      });
    });
    req.on('error', () => resolve(null));
    req.setTimeout(6000, () => { req.destroy(); resolve(null); });
  });
}

function _lrcNorm(s) {
  return (s || '').toLowerCase().replace(/[^a-z0-9 ]+/g, ' ').replace(/\s+/g, ' ').trim();
}

function _lrcArtistMatches(have, want) {
  const a = _lrcNorm(have); const b = _lrcNorm(want);
  if (!a || !b) return false;
  if (a === b) return true;
  // Allow "feat" / multi-artist by checking either side contains the other.
  if (a.includes(b) || b.includes(a)) return true;
  // Compare first artist token (handles "Drake & Future" vs "Drake")
  const af = a.split(/[&,]| feat | ft /)[0].trim();
  const bf = b.split(/[&,]| feat | ft /)[0].trim();
  if (af && bf && (af === bf || af.includes(bf) || bf.includes(af))) return true;
  // Compare squashed (no spaces) — handles uploader names like "FettyWap"
  // vs the lrclib artist "Fetty Wap", or "PostMalone" vs "Post Malone".
  const aSq = a.replace(/\s+/g, '');
  const bSq = b.replace(/\s+/g, '');
  if (aSq && bSq && (aSq === bSq || aSq.includes(bSq) || bSq.includes(aSq))) return true;
  return false;
}

function _lrclibSearch(query, expectedArtist) {
  return new Promise((resolve) => {
    const params = new URLSearchParams({ q: query });
    const req = https.get(`https://lrclib.net/api/search?${params}`, { headers: { 'User-Agent': 'DiscordBot/1.0' } }, (res) => {
      let raw = '';
      res.on('data', c => raw += c);
      res.on('end', () => {
        try {
          const arr = JSON.parse(raw);
          if (!Array.isArray(arr) || arr.length === 0) return resolve(null);
          // Require artist match when we have one. Without that gate, lrclib's
          // first result is often a different song that happens to share a title.
          let candidates = arr;
          if (expectedArtist) {
            candidates = arr.filter(x => _lrcArtistMatches(x.artistName, expectedArtist));
            if (!candidates.length) return resolve(null);
          }
          const synced = candidates.find(x => x.syncedLyrics) || null;
          const plain = candidates.find(x => x.plainLyrics) || null;
          if (synced) return resolve({ synced: synced.syncedLyrics, plain: synced.plainLyrics || null });
          if (plain) return resolve({ synced: null, plain: plain.plainLyrics });
          resolve(null);
        } catch { resolve(null); }
      });
    });
    req.on('error', () => resolve(null));
    req.setTimeout(6000, () => { req.destroy(); resolve(null); });
  });
}

async function fetchLyrics(rawTitle, rawArtist) {
  const cleanTitle = _cleanLyricTitle(rawTitle);
  const cleanArtist = _cleanLyricArtist(rawArtist);

  // 1) exact lookup with cleaned values
  let r = await _lrclibGet(cleanTitle, cleanArtist);
  if (r) return r;

  // 2) if title contains "Artist - Song", try splitting both ways
  const split = _splitTitleArtist(cleanTitle);
  if (split) {
    r = await _lrclibGet(split.right, split.left);
    if (r) return r;
    r = await _lrclibGet(split.left, split.right);
    if (r) return r;
  }

  // 3) fuzzy search — but always gate on the artist when we have one so we
  // don't return lyrics from a different song that shares a title.
  if (cleanArtist) {
    r = await _lrclibSearch(`${cleanArtist} ${cleanTitle}`, cleanArtist);
    if (r) return r;
    if (split) {
      r = await _lrclibSearch(`${split.left} ${split.right}`, cleanArtist);
      if (r) return r;
    }
    // Fall through to title-only search rather than refusing — songs like
    // Fetty Wap fail strict artist matching when YouTube uploaders differ.
  }

  // Title-only best-effort search.
  r = await _lrclibSearch(cleanTitle, null);
  if (r) return r;
  const split2 = _splitTitleArtist(cleanTitle);
  if (split2) {
    r = await _lrclibSearch(split2.right, null);
    if (r) return r;
    r = await _lrclibSearch(split2.left, null);
    if (r) return r;
  }

  return { synced: null, plain: null };
}

function httpFetch(method, url, headers = {}, body = null) {
  return new Promise((resolve, reject) => {
    try {
      const u = new URL(url);
      const opts = {
        method,
        hostname: u.hostname,
        port: u.port || (u.protocol === 'http:' ? 80 : 443),
        path: u.pathname + u.search,
        headers: { 'User-Agent': 'Mozilla/5.0 DiscordBot', ...headers }
      };
      if (body) opts.headers['Content-Length'] = Buffer.byteLength(body);
      const mod = u.protocol === 'http:' ? require('http') : https;
      const req = mod.request(opts, res => {
        let raw = '';
        res.on('data', c => raw += c);
        res.on('end', () => {
          let data = raw;
          try { if (res.headers['content-type']?.includes('json')) data = JSON.parse(raw); } catch {}
          resolve({ status: res.statusCode, headers: res.headers, data, raw });
        });
      });
      req.on('error', reject);
      req.setTimeout(15000, () => req.destroy(new Error('Request timed out')));
      if (body) req.write(body);
      req.end();
    } catch (e) { reject(e); }
  });
}

function safeMathEval(expr) {
  if (!/^[-+*/%().\d\s,eE\^Mathpisqrtabcoslgexpfnnloramioctwu]+$/.test(expr)) throw new Error('Invalid characters in expression');
  const sanitized = expr.replace(/\^/g, '**')
    .replace(/\bpi\b/gi, 'Math.PI').replace(/\be\b/g, 'Math.E')
    .replace(/\b(sqrt|cbrt|abs|sin|cos|tan|log|log2|log10|exp|floor|ceil|round|min|max|pow)\b/gi, 'Math.$1');
  // eslint-disable-next-line no-new-func
  const val = Function(`"use strict"; return (${sanitized})`)();
  if (typeof val !== 'number' || !isFinite(val)) throw new Error('Not a finite number');
  return val;
}

// 5-row block font for the /ascii slash command. Replaces the dead
// artii.herokuapp.com dependency so the command works offline.
const ASCII_FONT = {
  'A': [' ## ','#  #','####','#  #','#  #'],
  'B': ['### ','#  #','### ','#  #','### '],
  'C': [' ###','#   ','#   ','#   ',' ###'],
  'D': ['### ','#  #','#  #','#  #','### '],
  'E': ['####','#   ','### ','#   ','####'],
  'F': ['####','#   ','### ','#   ','#   '],
  'G': [' ###','#   ','# ##','#  #',' ###'],
  'H': ['#  #','#  #','####','#  #','#  #'],
  'I': ['###',' # ',' # ',' # ','###'],
  'J': ['####','   #','   #','#  #',' ## '],
  'K': ['#  #','# # ','##  ','# # ','#  #'],
  'L': ['#   ','#   ','#   ','#   ','####'],
  'M': ['#   #','## ##','# # #','#   #','#   #'],
  'N': ['#  #','## #','# ##','#  #','#  #'],
  'O': [' ## ','#  #','#  #','#  #',' ## '],
  'P': ['### ','#  #','### ','#   ','#   '],
  'Q': [' ## ','#  #','#  #','# ##',' ###'],
  'R': ['### ','#  #','### ','# # ','#  #'],
  'S': [' ###','#   ',' ## ','   #','### '],
  'T': ['#####','  #  ','  #  ','  #  ','  #  '],
  'U': ['#  #','#  #','#  #','#  #',' ## '],
  'V': ['#   #','#   #','#   #',' # # ','  #  '],
  'W': ['#   #','#   #','# # #','## ##','#   #'],
  'X': ['#  #',' ## ','  # ',' ## ','#  #'],
  'Y': ['#   #',' # # ','  #  ','  #  ','  #  '],
  'Z': ['####','   #','  # ',' #  ','####'],
  '0': [' ## ','#  #','#  #','#  #',' ## '],
  '1': [' # ','## ',' # ',' # ','###'],
  '2': [' ## ','#  #','  # ',' #  ','####'],
  '3': ['### ','   #',' ## ','   #','### '],
  '4': ['#  #','#  #','####','   #','   #'],
  '5': ['####','#   ','### ','   #','### '],
  '6': [' ###','#   ','### ','#  #',' ## '],
  '7': ['####','   #','  # ',' #  ',' #  '],
  '8': [' ## ','#  #',' ## ','#  #',' ## '],
  '9': [' ## ','#  #',' ###','   #','### '],
  ' ': ['  ','  ','  ','  ','  '],
  '!': ['#','#','#',' ','#'],
  '?': [' ## ','#  #','  # ','    ','  # '],
  '.': ['  ','  ','  ','  ','# '],
  ',': ['  ','  ','  ',' #','# '],
};
function renderAsciiArt(text) {
  const chars = (text || '').toUpperCase().split('').map(c => ASCII_FONT[c] || ASCII_FONT['?']);
  if (!chars.length) return '(empty)';
  const rows = [];
  for (let r = 0; r < 5; r++) rows.push(chars.map(g => g[r]).join(' '));
  return rows.join('\n');
}

function rest(method, path, data, token) {
  return new Promise((resolve, reject) => {
    const body = data ? JSON.stringify(data) : null;
    const req = https.request({
      hostname: 'discord.com',
      path: `/api/v10${path}`,
      method,
      headers: {
        'Authorization': `Bot ${token}`,
        'Content-Type': 'application/json',
        ...(body ? { 'Content-Length': Buffer.byteLength(body) } : {})
      }
    }, res => {
      let raw = '';
      res.on('data', c => raw += c);
      res.on('end', () => {
        try { resolve({ status: res.statusCode, data: raw ? JSON.parse(raw) : {} }); }
        catch { resolve({ status: res.statusCode, data: {} }); }
      });
    });
    req.on('error', reject);
    if (body) req.write(body);
    req.end();
  });
}

// Downloads a video URL and merges in the separate audio stream when needed.
// Reddit DASH and Redgifs CDN both serve video-only mp4s with audio at a sibling URL.
async function _downloadWithAudio(videoUrl) {
  let extraHeaders = {};
  if (/redgifs\.com/i.test(videoUrl)) {
    const tok = await _getRedgifsToken();
    if (tok) extraHeaders['Authorization'] = `Bearer ${tok}`;
    extraHeaders['Referer'] = 'https://www.redgifs.com/';
  }
  const buf = await downloadBuffer(videoUrl, 0, extraHeaders);

  let audioCandidates = [];
  if (/v\.redd\.it/i.test(videoUrl)) {
    audioCandidates = [videoUrl.replace(/\/DASH_\d+\.mp4.*$/, '/DASH_audio.mp4')];
  } else if (/redgifs\.com/i.test(videoUrl)) {
    // Try both .m4a (standard) and .hd.m4a (newer clips) regardless of input URL variant.
    const base  = videoUrl.replace(/(?:\.hd)?\.mp4(\?.*)?$/i, '.m4a');
    const hdAlt = videoUrl.replace(/(?:\.hd)?\.mp4(\?.*)?$/i, '.hd.m4a');
    audioCandidates = [base, hdAlt];
  }

  if (!audioCandidates.length) return buf;

  let audioBuf = null;
  for (const audioUrl of audioCandidates) {
    // Retry once on transient network errors; skip on HTTP 4xx (no audio track).
    for (let attempt = 0; attempt < 2; attempt++) {
      try {
        audioBuf = await downloadBuffer(audioUrl, 0, extraHeaders);
        break;
      } catch (e) {
        const isHttpErr = /HTTP \d{3}/.test(e.message);
        if (isHttpErr || attempt === 1) break; // HTTP error or second attempt failed — move on
      }
    }
    if (audioBuf) break;
  }
  // For Redgifs, a missing audio track means the content will be silent — return null
  // so callers can fall back to the watch URL (Redgifs player handles audio natively).
  // For other sources (e.g. v.redd.it) the clip may legitimately have no audio, so return buf.
  if (!audioBuf) return /redgifs\.com/i.test(videoUrl) ? null : buf;

  const id = `merge_${Date.now()}`;
  const tmpDir = require('os').tmpdir();
  const vPath = path.join(tmpDir, `${id}_v.mp4`);
  const aPath = path.join(tmpDir, `${id}_a`);
  const oPath = path.join(tmpDir, `${id}_out.mp4`);
  fs.writeFileSync(vPath, buf);
  fs.writeFileSync(aPath, audioBuf);
  try {
    await new Promise((resolve, reject) => {
      execFile(getBin('ffmpeg'), [
        '-i', vPath, '-i', aPath,
        '-c:v', 'copy', '-c:a', 'aac', '-shortest', '-y', oPath,
      ], { timeout: 30000 }, (err) => err ? reject(err) : resolve());
    });
    return fs.readFileSync(oPath);
  } finally {
    for (const p of [vPath, aPath, oPath]) try { fs.unlinkSync(p); } catch {}
  }
}

// Download a remote URL into a Buffer (max 20 MB, 25 s timeout). Follows redirects.
function downloadBuffer(url, _hops, extraHeaders) {
  _hops = _hops || 0;
  return new Promise((resolve, reject) => {
    const MAX = 20 * 1024 * 1024;
    const hdrs = { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36', ...(extraHeaders || {}) };
    if (/redgifs\.com/i.test(url)) hdrs['Referer'] = 'https://www.redgifs.com/';
    const req = https.get(url, { headers: hdrs }, res => {
      if (res.statusCode >= 300 && res.statusCode < 400 && res.headers.location && _hops < 3) {
        res.resume(); req.destroy();
        return downloadBuffer(res.headers.location, _hops + 1, extraHeaders).then(resolve, reject);
      }
      if (res.statusCode >= 400) { res.resume(); return reject(new Error(`HTTP ${res.statusCode}`)); }
      const cl = parseInt(res.headers['content-length'] || '0', 10);
      if (cl > MAX) { res.resume(); return reject(new Error('too_large')); }
      let total = 0;
      const chunks = [];
      res.on('data', chunk => {
        total += chunk.length;
        if (total > MAX) { req.destroy(); return reject(new Error('too_large')); }
        chunks.push(chunk);
      });
      res.on('end', () => resolve(Buffer.concat(chunks)));
    });
    req.on('error', reject);
    req.setTimeout(25000, () => { req.destroy(); reject(new Error('timeout')); });
  });
}

// Send a multipart/form-data request to Discord (required for binary file attachments).
function restMultipart(method, path, payloadJson, files, token) {
  return new Promise((resolve, reject) => {
    const boundary = `----DiscordFormBoundary${Date.now()}`;
    const parts = [];
    // JSON payload part
    const jsonStr = JSON.stringify(payloadJson);
    parts.push(Buffer.from(
      `--${boundary}\r\nContent-Disposition: form-data; name="payload_json"\r\nContent-Type: application/json\r\n\r\n${jsonStr}\r\n`
    ));
    // File parts
    files.forEach((f, i) => {
      parts.push(Buffer.from(
        `--${boundary}\r\nContent-Disposition: form-data; name="files[${i}]"; filename="${f.name}"\r\nContent-Type: ${f.mime || 'application/octet-stream'}\r\n\r\n`
      ));
      parts.push(f.data);
      parts.push(Buffer.from('\r\n'));
    });
    parts.push(Buffer.from(`--${boundary}--\r\n`));
    const body = Buffer.concat(parts);
    const req = https.request({
      hostname: 'discord.com',
      path: `/api/v10${path}`,
      method,
      headers: {
        'Authorization': `Bot ${token}`,
        'Content-Type': `multipart/form-data; boundary=${boundary}`,
        'Content-Length': body.length,
      }
    }, res => {
      let raw = '';
      res.on('data', c => raw += c);
      res.on('end', () => {
        try {
          const parsed = raw ? JSON.parse(raw) : {};
          if (res.statusCode >= 400) return reject(Object.assign(new Error(`HTTP ${res.statusCode}`), { status: res.statusCode, body: parsed }));
          resolve({ status: res.statusCode, data: parsed });
        } catch { resolve({ status: res.statusCode, data: {} }); }
      });
    });
    req.on('error', reject);
    req.write(body);
    req.end();
  });
}

function reply(interaction, token, content, ephemeral = false) {
  return rest('POST', `/interactions/${interaction.id}/${interaction.token}/callback`,
    { type: 4, data: { content, flags: ephemeral ? 64 : 0 } }, token);
}

function replyEmbed(interaction, token, embed, content = '') {
  return rest('POST', `/interactions/${interaction.id}/${interaction.token}/callback`,
    { type: 4, data: { content, embeds: [embed] } }, token);
}

function getOpt(interaction, name) {
  return (interaction.data?.options || []).find(o => o.name === name)?.value;
}

function msToTime(ms) {
  const s = Math.floor(ms / 1000);
  const m = Math.floor(s / 60);
  const h = Math.floor(m / 60);
  const d = Math.floor(h / 24);
  if (d > 0) return `${d}d ${h % 24}h ${m % 60}m`;
  if (h > 0) return `${h}h ${m % 60}m`;
  return `${m}m ${s % 60}s`;
}

// ─── Lovense Connect helpers ───

function _lovenseGet(baseUrl, path) {
  return new Promise((resolve, reject) => {
    const mod = /^https/i.test(baseUrl) ? https : http;
    const parsed = new URL(baseUrl + path);
    const req = mod.get({
      hostname: parsed.hostname, port: parsed.port || (parsed.protocol === 'https:' ? 443 : 80),
      path: parsed.pathname + parsed.search,
    }, res => {
      let body = '';
      res.on('data', d => body += d);
      res.on('end', () => { try { resolve(JSON.parse(body)); } catch { resolve({}); } });
    });
    req.on('error', reject);
    req.setTimeout(5000, () => { req.destroy(); reject(new Error('Lovense Connect timeout')); });
  });
}

function _lovensePost(baseUrl, path, body) {
  return new Promise((resolve, reject) => {
    const mod = /^https/i.test(baseUrl) ? https : http;
    const parsed = new URL(baseUrl + path);
    const data = JSON.stringify(body);
    const req = mod.request({
      hostname: parsed.hostname, port: parsed.port || (parsed.protocol === 'https:' ? 443 : 80),
      path: parsed.pathname, method: 'POST',
      headers: { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(data) },
    }, res => {
      let out = '';
      res.on('data', d => out += d);
      res.on('end', () => { try { resolve(JSON.parse(out)); } catch { resolve({}); } });
    });
    req.on('error', reject);
    req.setTimeout(5000, () => { req.destroy(); reject(new Error('Lovense Connect timeout')); });
    req.write(data);
    req.end();
  });
}

// ─── BOT FACTORY ───
// Returns an independent bot instance with its own WebSocket + music state.

function createBot() {
  // ── Per-instance state ──
  let ws = null;
  let heartbeatInterval = null;
  let sessionId = null;
  let lastSeq = null;
  let botUser = null;
  let _token = null;
  let _onStatus = null;
  let reconnectTimer = null;
  let dead = false;
  let startTime = Date.now();
  let _trackChangeCb = null;
  let _resumeGatewayUrl = null; // Discord-provided resume URL from READY
  let _reconnectAttempts = 0;   // exponential backoff counter
  let _heartbeatAcked = true;   // tracks whether last heartbeat was acknowledged

  const voiceAdapters = new Map();    // guildId -> adapter methods
  const voiceConnections = new Map(); // guildId -> VoiceConnection (legacy)
  const voicePlayers = new Map();     // guildId -> AudioPlayer (legacy)
  const memberVoiceStates = new Map();// `${guildId}:${userId}` -> channelId
  const guildMusic = new Map();       // guildId -> state
  const pendingVoice = new Map();     // guildId -> { vsu, vsru } – for direct voice join
  const activeVoice = new Map();      // guildId -> active voice session
  const nowPlayingMsgs = new Map();   // guildId -> { channelId, messageId }
  const giveawayEntries = new Map();  // `${guildId}:${messageId}` -> Set<userId>
  const activeGiveaways = new Map(); // `${guildId}:${messageId}` -> { prize, winnerCount, requiredRole, channelId, endsAt, guildId }
  const applyConfigs    = new Map(); // configKey -> { questions, staffChannelId, staffRoleId, title, guildId }
  const stickyMessages  = new Map(); // channelId -> { content, embedTitle, color, guildId }
  const stickyPinned    = new Map(); // channelId -> lastPostedMessageId
  const warnLog       = new Map();   // `${guildId}:${userId}` -> string[]
  const guildAutoRole = new Map();   // guildId -> roleId
  const guildWelcome  = new Map();   // guildId -> {channelId, message}
  const guildGoodbye  = new Map();   // guildId -> {channelId, message}
  const reactionRoles = new Map();   // `${guildId}:${messageId}` -> {emoji: roleId}
  const starboards    = new Map();   // guildId -> {channelId, threshold, posted: Set}
  const autoDelete    = new Map();   // channelId -> seconds
  const nsfwChannels  = new Set();   // channelId — persisted to nsfw-state.json
  const nsfwRoles     = new Map();   // guildId -> roleId
  // Restore previously-enabled channels and roles so toggle only needs to be run once
  { const s = _loadNsfwState();
    (s.channels || []).forEach(id => nsfwChannels.add(id));
    (s.roles    || []).forEach(([g, r]) => nsfwRoles.set(g, r)); }
  const guildAutoplay = new Map();   // guildId -> bool
  const helpSessions   = new Map();   // sessionId -> { pages, page, userId }
  const triviaSessions = new Map();   // channelId -> { correctAnswer, correctIndex, question, category, questioner, expiresAt }
  const guildModRoles  = new Map();   // guildId -> Set<roleId>
  const economy       = new Map();   // userId -> { coins, xp, level, rep, lastDaily, lastWork, lastSteal, lastRep, spouse }
  const proposals     = new Map();   // `${targetId}:${guildId}` -> { from, time }
  const sextConfig         = new Map();   // guildId -> { name, persona, style }
  const sextHistory        = new Map();   // userId  -> { messages: [], dmChannelId }
  const sextChannelSessions = new Map();  // "guildId:userId" -> { messages: [], channelId, cfg, sentIds }
  const lovenseConfig      = new Map();   // guildId -> { url }
  const nsfwAutopost  = new Map();   // `${guildId}:__ap__${1-5}` -> { postFn, category/categories, intervalMin, targetChannelId }
  const dtState       = new Map();   // guildId -> { conn, player, proc, ff, vcId, dtType }

  // Tear down yt-dlp + ffmpeg processes; unpipe first to avoid in-flight write errors.
  function _dtKill(dt) {
    if (!dt) return;
    try { if (dt.proc) { dt.proc.stdout.unpipe(); dt.proc.kill(); } } catch {}
    try { if (dt.ff)   dt.ff.kill(); } catch {}
    try { if (dt.player) { dt.player.removeAllListeners(); dt.player.stop(); } } catch {}
  }
  // Full stop: kill processes AND destroy the voice connection.
  function _dtStop(guildId) {
    const dt = dtState.get(guildId);
    if (!dt) return;
    _dtKill(dt);
    try { if (dt.conn) dt.conn.destroy(); } catch {}
    dtState.delete(guildId);
  }
  // Global 1-minute tick — fires each feed when currentUTCMinute % feed.intervalMin === 0,
  // so all 3-min feeds fire together, all 5-min together, etc.
  let _apGlobalTicker = null;
  let _apGlobalAlignTimer = null;
  function _apTickAll() {
    if (!nsfwAutopost.size) { clearInterval(_apGlobalTicker); _apGlobalTicker = null; return; }
    const nowMin = Math.floor(Date.now() / 60000);
    for (const feed of nsfwAutopost.values()) {
      if (nowMin % feed.intervalMin === 0 && typeof feed.postFn === 'function') feed.postFn();
    }
  }
  function _apEnsureTicker() {
    if (_apGlobalTicker) return;
    const msUntilNextMin = 60000 - (Date.now() % 60000);
    clearTimeout(_apGlobalAlignTimer);
    _apGlobalAlignTimer = setTimeout(() => {
      _apTickAll();
      _apGlobalTicker = setInterval(_apTickAll, 60000);
    }, msUntilNextMin);
  }
  function _apNextSlot(gid) {
    for (let i = 1; i <= 5; i++) {
      if (!nsfwAutopost.has(`${gid}:__ap__${i}`)) return i;
    }
    return null;
  }
  function _apGuildFeeds(gid) {
    return [...nsfwAutopost.entries()].filter(([k]) => k.startsWith(`${gid}:__ap__`));
  }
  const nsfwPostedIds = _loadNsfwDedup(); // guildId -> Set<string> — dedupe recently posted content, persisted
  const nsfwCooldowns = new Map();  // userId -> last command timestamp
  const nsfwCommandStats = new Map(); // `${guildId}:${cmd}` -> count
  const VISUAL_RE = /\b(send|show|pic(ture|s)?|photo|image|gif|video|let me see|see you|look at|nudes?|naked|body|selfie|tit|boob|ass|pussy)\b/i;
  const ASMR_RE   = /\b(asmr|moan(ing)?|audio|whisper|talk to me|breath(e)?|hear you|voice|listen|sound|make a sound|make noise)\b/i;

  function getEco(uid) {
    if (!economy.has(uid)) economy.set(uid, { coins: 0, xp: 0, level: 1, rep: 0, lastDaily: 0, lastWork: 0, lastSteal: 0, lastRep: 0, spouse: null });
    return economy.get(uid);
  }
  function fmtMs(ms) {
    const h = Math.floor(ms / 3600000), m = Math.floor((ms % 3600000) / 60000);
    return h > 0 ? `${h}h ${m}m` : `${m}m`;
  }

  // ── Live-lyric bot status ──
  // Discord gateway allows ~5 presence updates per 20s (one every ~4s sustained).
  // Push the throttle as low as we safely can so the bot RPC tracks the in-app
  // lyric card closely. The in-app card is NOT throttled — it gets every chunk in real time.
  const PRESENCE_MIN_INTERVAL_MS = 4500;
  // Audio pipeline latency: yt-dlp spawn + FFmpeg + Discord voice buffer means the
  // listener hears each line ~3-4s after our trackStart timestamp. Shifting
  // trackStart into the future by this amount delays the lyric scheduler so
  // lines appear in step with what's actually being heard. Tune up if lyrics
  // still run ahead, down if they run behind.
  const AUDIO_PIPELINE_DELAY_MS = 6000;
  // Rich-presence default: shows as a profile card with details/state/elapsed-time.
  // (Image assets require registering large_image/small_image keys in the Discord
  //  developer portal under Rich Presence > Art Assets — text fields work without.)
  function buildDefaultActivity() {
    return {
      name: 'Discord Server Creator',
      type: 0, // Playing
      details: 'Spinning up servers',
      state: 'AI-powered • Music • Embeds',
      timestamps: { start: startTime },
    };
  }
  // Fun rotating idle status — every 60s the bot picks a new line. Mix of
  // Playing/Watching/Listening/Competing types so the prefix changes too,
  // making each status visually distinct.
  const FUN_STATUSES = [
    { name: 'with the off button', type: 0 },
    { name: 'paint dry, professionally', type: 3 },
    { name: 'to your inner thoughts', type: 2 },
    { name: 'hide and seek with mods', type: 0 },
    { name: 'you sleep', type: 3 },
    { name: 'the void scream back', type: 2 },
    { name: 'in the staff-only channels', type: 0 },
    { name: 'a thumb war for dominance', type: 5 },
    { name: 'silence... too much silence', type: 2 },
    { name: 'every message ever sent here', type: 3 },
    { name: 'with fire (do not try this)', type: 0 },
    { name: 'an existential crisis', type: 5 },
    { name: 'the WiFi load', type: 3 },
    { name: 'lofi beats to chill servers to', type: 2 },
    { name: 'in the kitchen, definitely cooking', type: 0 },
    { name: 'whales sing the encyclopedia', type: 2 },
  ];
  let _funRotateTimer = null;
  let _funIdx = 0;
  function _rotateFunStatus() {
    if (_lyricOwner) return; // music presence wins; rotation paused
    const s = FUN_STATUSES[_funIdx % FUN_STATUSES.length];
    _funIdx++;
    sendPresence({ name: s.name, type: s.type, timestamps: { start: startTime } });
  }
  function startFunRotation() {
    if (_funRotateTimer) return;
    _rotateFunStatus();                                // immediate first one
    _funRotateTimer = setInterval(_rotateFunStatus, 60_000);
  }
  function stopFunRotation() {
    if (_funRotateTimer) { clearInterval(_funRotateTimer); _funRotateTimer = null; }
  }
  const LYRIC_CHUNK_MAX = 60;   // chars per displayed chunk
  const LYRIC_CHUNK_MIN_MS = 1100;  // minimum dwell per chunk
  let _lyricOwner = null;  // { guildId, token, track, trackStart, chunks, lastIdx, lastSent }
  let _lyricTimer = null;
  let _lyricStatusDirty = false;
  let _lyricChangeCb = null;

  function sendPresence(activity) {
    if (!ws || ws.readyState !== WebSocket.OPEN) return;
    send({ op: 3, d: { since: null, activities: activity ? [activity] : [], status: 'online', afk: false } });
  }

  // Resolve an arbitrary image URL to a Discord-hosted asset reference suitable
  // for activity assets.large_image. Discord requires external images to first
  // be registered via POST /applications/{app_id}/external-assets, which returns
  // a signed external_asset_path. Without going through this endpoint, the bare
  // mp:external/... form silently fails to render. Results are cached per URL.
  const _externalAssetCache = new Map(); // url -> "mp:external/<hash>/..."
  // Spotify Client-Credentials lookup so the bot RPC shows the actual album art
  // (not the YouTube thumbnail). Same credentials as the discord_rpc.py script.
  // Token is cached until ~30s before expiry; results are cached per (track|artist).
  const SPOTIFY_CLIENT_ID = 'e8ab66a616b54d97882d90864fbe2fb5';
  const SPOTIFY_CLIENT_SECRET = '1dca3d2bce0743ef93112382e8936c30';
  let _spotifyToken = null;
  let _spotifyTokenExp = 0;
  const _spotifyArtCache = new Map(); // key=`${name}|${artist}` -> image URL or null
  function _httpsPost(host, path, body, headers) {
    return new Promise((resolve, reject) => {
      const req = https.request({ hostname: host, path, method: 'POST', headers: { 'Content-Length': Buffer.byteLength(body), ...headers } }, res => {
        let raw = ''; res.on('data', c => raw += c);
        res.on('end', () => { try { resolve({ status: res.statusCode, data: raw ? JSON.parse(raw) : {} }); } catch { resolve({ status: res.statusCode, data: {} }); } });
      });
      req.on('error', reject); req.write(body); req.end();
    });
  }
  function _httpsGetJson(url, headers) {
    return new Promise((resolve, reject) => {
      const u = new URL(url);
      const req = https.request({ hostname: u.hostname, path: u.pathname + u.search, method: 'GET', headers: headers || {} }, res => {
        let raw = ''; res.on('data', c => raw += c);
        res.on('end', () => { try { resolve({ status: res.statusCode, data: raw ? JSON.parse(raw) : {} }); } catch { resolve({ status: res.statusCode, data: {} }); } });
      });
      req.on('error', reject); req.end();
    });
  }
  async function _getSpotifyToken() {
    if (_spotifyToken && Date.now() < _spotifyTokenExp - 30_000) return _spotifyToken;
    const basic = Buffer.from(`${SPOTIFY_CLIENT_ID}:${SPOTIFY_CLIENT_SECRET}`).toString('base64');
    const res = await _httpsPost('accounts.spotify.com', '/api/token', 'grant_type=client_credentials', {
      Authorization: `Basic ${basic}`,
      'Content-Type': 'application/x-www-form-urlencoded',
    });
    if (res.status !== 200 || !res.data.access_token) {
      console.warn('[Spotify] token failed', res.status, JSON.stringify(res.data).slice(0, 200));
      return null;
    }
    _spotifyToken = res.data.access_token;
    _spotifyTokenExp = Date.now() + (res.data.expires_in || 3600) * 1000;
    return _spotifyToken;
  }
  async function fetchSpotifyAlbumArt(trackName, artistName) {
    if (!trackName) return null;
    const key = `${(trackName || '').toLowerCase()}|${(artistName || '').toLowerCase()}`;
    if (_spotifyArtCache.has(key)) return _spotifyArtCache.get(key);
    try {
      const tok = await _getSpotifyToken();
      if (!tok) { _spotifyArtCache.set(key, null); return null; }
      const q = artistName ? `track:${trackName} artist:${artistName}` : trackName;
      const res = await _httpsGetJson(`https://api.spotify.com/v1/search?q=${encodeURIComponent(q)}&type=track&limit=1`,
        { Authorization: `Bearer ${tok}` });
      const img = res?.data?.tracks?.items?.[0]?.album?.images?.[0]?.url || null;
      _spotifyArtCache.set(key, img);
      return img;
    } catch (e) {
      console.warn('[Spotify] art lookup failed', e.message);
      _spotifyArtCache.set(key, null);
      return null;
    }
  }

  async function resolveExternalAssetPath(url) {
    if (!url || typeof url !== 'string' || !/^https?:\/\//i.test(url)) return null;
    if (_externalAssetCache.has(url)) return _externalAssetCache.get(url);
    const appId = botUser?.id;
    if (!appId || !_token) return null;
    try {
      const res = await rest('POST', `/applications/${appId}/external-assets`, { urls: [url] }, _token);
      const path = Array.isArray(res?.data) && res.data[0]?.external_asset_path;
      const asset = path ? `mp:${path}` : null;
      if (!asset) {
        console.warn('[RPC] external-assets failed for', url, 'status=', res?.status, 'body=', JSON.stringify(res?.data).slice(0, 300));
      }
      _externalAssetCache.set(url, asset);
      return asset;
    } catch (e) {
      console.warn('[RPC] external-assets error for', url, e.message);
      _externalAssetCache.set(url, null);
      return null;
    }
  }

  function _splitLineIntoChunks(text) {
    if (!text) return [text];
    if (text.length <= LYRIC_CHUNK_MAX) return [text];
    const words = text.split(/\s+/);
    const out = [];
    let cur = '';
    for (const w of words) {
      if (!cur) { cur = w; continue; }
      if (cur.length + 1 + w.length > LYRIC_CHUNK_MAX) { out.push(cur); cur = w; }
      else cur += ' ' + w;
    }
    if (cur) out.push(cur);
    return out;
  }

  // Expand parsed [{t, text}] into [{t, text, lineIdx, chunkIdx, chunkOf}] where each
  // chunk gets its own scheduled time inside the parent line's window.
  function _buildChunkSchedule(lines) {
    const out = [];
    for (let i = 0; i < lines.length; i++) {
      const ln = lines[i];
      const next = lines[i + 1];
      const winMs = Math.max(LYRIC_CHUNK_MIN_MS, ((next ? next.t : ln.t + 4) - ln.t) * 1000);
      const parts = _splitLineIntoChunks(ln.text);
      const per = winMs / parts.length;
      parts.forEach((p, j) => {
        out.push({ t: ln.t + (j * per) / 1000, text: p, lineIdx: i, chunkIdx: j, chunkOf: parts.length, total: lines.length });
      });
    }
    return out;
  }

  async function startLyricStatus(guildId, track) {
    stopFunRotation();
    const tokenSym = Symbol('lyricOwner');
    _lyricOwner = { guildId, token: tokenSym, track: track || {}, trackStart: Date.now() + AUDIO_PIPELINE_DELAY_MS, chunks: [], lastIdx: -1, lastSent: 0, artAsset: null, pendingChunks: [], lastSentText: null, trackEnd: 0 };
    if (_lyricChangeCb) { try { _lyricChangeCb(guildId, { type: 'reset', track: { name: track.name||track.title||'', artist: track.artist||'', artwork: track.artwork||null } }); } catch {} }
    // Send an immediate "now playing" presence so the rotating fun statuses
    // can't bleed through (e.g. while we're awaiting lyrics, or for tracks
    // without any lyric data at all). The drain queue uses this baseline too.
    _enqueueLyricPresence({ text: '' });
    // Kick off album-art resolution in parallel. We prefer the actual Spotify
    // album art (matches the discord_rpc.py behaviour) and fall back to whatever
    // the track shipped with (e.g. YouTube thumbnail) if Spotify has no match.
    // First presence send may fire before this resolves; once resolved, drains
    // pick it up. Re-send presence immediately when art arrives so users see it.
    (async () => {
      const spotArt = await fetchSpotifyAlbumArt(track.name || track.title || '', track.artist || '').catch(() => null);
      const artUrl = spotArt || (typeof track?.artwork === 'string' && /^https?:\/\//i.test(track.artwork) ? track.artwork : null);
      if (!artUrl) return;
      // Stash the resolved Spotify URL on the owner so the deploy-tab UI / track
      // metadata callback can also surface the proper album art (similar player
      // shows it too — see _trackChangeCb -> bot-now-playing IPC payload).
      if (_lyricOwner && _lyricOwner.token === tokenSym) {
        _lyricOwner.track = { ..._lyricOwner.track, artwork: artUrl };
        if (_trackChangeCb) { try { _trackChangeCb(guildId, _lyricOwner.track); } catch {} }
      }
      const asset = await resolveExternalAssetPath(artUrl).catch(() => null);
      if (_lyricOwner && _lyricOwner.token === tokenSym) {
        _lyricOwner.artAsset = asset;
        if (asset) _enqueueLyricPresence({ text: '' });
      }
    })();
    try {
      const { synced } = await fetchLyrics(track.name || track.title || '', track.artist || '');
      if (!_lyricOwner || _lyricOwner.token !== tokenSym) return;
      const lines = parseLrcLines(synced);
      _lyricOwner.chunks = _buildChunkSchedule(lines);
      // Derive track end from the last LRC line + 20s buffer (instrumentation/outro).
      // Mirrors discord_rpc.py's use of duration to populate timestamps.end so the
      // bot card shows a real progress bar (elapsed / remaining), not just elapsed.
      if (lines.length) {
        const lastT = lines[lines.length - 1].t || 0;
        _lyricOwner.trackEnd = _lyricOwner.trackStart + Math.round((lastT + 20) * 1000);
      }
      if (_lyricChangeCb) { try { _lyricChangeCb(guildId, { type: 'loaded', lineCount: lines.length, chunkCount: _lyricOwner.chunks.length }); } catch {} }
      // Re-send presence now that we have the end timestamp + lyrics ready.
      _enqueueLyricPresence({ text: '' });
    } catch {}
    _scheduleNextLyricTick();
  }

  function stopLyricStatus() {
    const wasGuild = _lyricOwner?.guildId;
    _lyricOwner = null;
    if (_lyricTimer) { clearTimeout(_lyricTimer); _lyricTimer = null; }
    if (_drainTimer) { clearTimeout(_drainTimer); _drainTimer = null; }
    _lyricStatusDirty = false;
    startFunRotation();                              // resume rotating fun statuses
    if (wasGuild && _lyricChangeCb) { try { _lyricChangeCb(wasGuild, { type: 'stop' }); } catch {} }
  }

  // ── No-skip lyric presence queue ──
  // Discord's gateway caps presence updates at ~5/20s. When lyrics fire faster
  // than that, queue them and drain at the rate-limit floor so every line still
  // shows on the bot RPC (it just lags behind real playback during dense runs).
  let _drainTimer = null;
  function _enqueueLyricPresence(chunk) {
    if (!_lyricOwner) return;
    _lyricOwner.pendingChunks.push(chunk);
    _drainLyricPresence();
  }
  // Force-update interval: even if the lyric text hasn't changed, refresh the
  // presence every 10s so progress/time stays in sync (matches discord_rpc.py).
  const PRESENCE_STALE_MS = 10_000;
  function _drainLyricPresence() {
    if (_drainTimer) return;
    if (!_lyricOwner || !_lyricOwner.pendingChunks.length) return;
    const wait = Math.max(0, PRESENCE_MIN_INTERVAL_MS - (Date.now() - _lyricOwner.lastSent));
    _drainTimer = setTimeout(() => {
      _drainTimer = null;
      if (!_lyricOwner || !_lyricOwner.pendingChunks.length) return;
      const c = _lyricOwner.pendingChunks.shift();
      // Dedupe identical lyric text — but always allow a re-send if the last
      // send is stale (>10s) so timestamps stay accurate.
      const stateText = _buildStateText(c);
      const stale = (Date.now() - _lyricOwner.lastSent) >= PRESENCE_STALE_MS;
      if (stateText === _lyricOwner.lastSentText && !stale) {
        if (_lyricOwner.pendingChunks.length) _drainLyricPresence();
        return;
      }
      _sendLyricPresence(c, stateText);
      _lyricOwner.lastSent = Date.now();
      _lyricOwner.lastSentText = stateText;
      _lyricStatusDirty = true;
      if (_lyricOwner.pendingChunks.length) _drainLyricPresence();
    }, wait);
  }

  // Trim a lyric chunk to fit Discord's 128-char state limit at a word boundary,
  // mirroring discord_rpc.py: `lyric[:127].rsplit(" ", 1)[0]` if too long, else
  // the lyric verbatim; falls back to "..." for empty/short text.
  function _buildStateText(c) {
    const raw = (c?.text || '').trim();
    if (!raw || raw.length < 2) return '...';
    if (raw.length <= 128) return raw;
    const cut = raw.slice(0, 127);
    const sp = cut.lastIndexOf(' ');
    return sp > 0 ? cut.slice(0, sp) : cut;
  }

  function _sendLyricPresence(c, stateText) {
    const owner = _lyricOwner; if (!owner) return;
    const t = owner.track || {};
    const trackName = (t.name || t.title || 'Unknown track').slice(0, 128);
    const artistName = (t.artist || 'Unknown artist').slice(0, 128);
    const text = stateText != null ? stateText : _buildStateText(c);
    const nextTrack = guildMusic.get(owner.guildId)?.queue?.[0];
    const upNextLabel = nextTrack
      ? `${(nextTrack.name || nextTrack.title || 'Unknown')}${nextTrack.artist ? ' - ' + nextTrack.artist : ''}`
      : null;
    const timestamps = owner.trackEnd
      ? { start: owner.trackStart, end: owner.trackEnd }
      : { start: owner.trackStart };
    const assets = {};
    if (owner.artAsset) assets.large_image = owner.artAsset;
    if (upNextLabel) assets.large_text = `Up next: ${upNextLabel}`.slice(0, 128);
    const payload = {
      name: `${trackName} by ${artistName}`.slice(0, 128),
      type: 2,
      state: text,
      timestamps,
    };
    if (Object.keys(assets).length) payload.assets = assets;
    sendPresence(payload);
  }

  function _scheduleNextLyricTick() {
    if (_lyricTimer) { clearTimeout(_lyricTimer); _lyricTimer = null; }
    const owner = _lyricOwner;
    if (!owner) return;
    if (!owner.chunks.length) { _lyricTimer = setTimeout(_scheduleNextLyricTick, 1500); return; }
    const posS = (Date.now() - owner.trackStart) / 1000;
    let idx = -1;
    for (let i = 0; i < owner.chunks.length; i++) {
      if (owner.chunks[i].t <= posS) idx = i;
      else break;
    }
    if (idx > owner.lastIdx) {
      const c = owner.chunks[idx];
      owner.lastIdx = idx;
      // In-app card: send every chunk immediately, no rate limit.
      if (_lyricChangeCb) {
        try { _lyricChangeCb(owner.guildId, { type: 'line', text: c.text, lineIdx: c.lineIdx, chunkIdx: c.chunkIdx, chunkOf: c.chunkOf, total: c.total, position: posS }); } catch {}
      }
      // Bot RPC: queue every chunk so none are dropped; the drain timer paces
      // sends to Discord's gateway rate limit (~4.5s minimum spacing).
      _enqueueLyricPresence(c);
    }
    // Sleep until the next chunk boundary (or 2s if we're at the end).
    const next = owner.chunks[idx + 1];
    let waitMs;
    if (next) {
      waitMs = Math.max(50, (next.t - posS) * 1000);
    } else {
      waitMs = 2000;
    }
    _lyricTimer = setTimeout(_scheduleNextLyricTick, waitMs);
  }

  function onLyricChange(cb) { _lyricChangeCb = cb; }

  // ── Music state helper ──
  function getMusicState(guildId) {
    if (!guildMusic.has(guildId)) {
      guildMusic.set(guildId, {
        queue: [],
        nowPlaying: null,
        player: null,
        connection: null,
        volume: 0.5,
        loop: false,
        loopAll: false,
        shuffle: false,
        paused: false,
        channelId: null,
        ytProcess: null,
        filters: { bassboost: false, chipmunk: false, vaporwave: false, slowed: false, '8d': false, reverb: false, earrape: false },
        seekSeconds: null,
        trackStartedAt: null,
        trackSeekBase: 0,
        pausedAt: null,
      });
    }
    return guildMusic.get(guildId);
  }

  function _onTrackChange(guildId, track) {
    if (_trackChangeCb) { try { _trackChangeCb(guildId, track); } catch {} }
  }

  // ── Voice adapter factory ──
  function createVoiceAdapter(guildId) {
    return (methods) => {
      voiceAdapters.set(guildId, methods);
      return {
        sendPayload(data) {
          if (ws && ws.readyState === WebSocket.OPEN) {
            ws.send(JSON.stringify(data));
            return true;
          }
          return false;
        },
        destroy() { voiceAdapters.delete(guildId); }
      };
    };
  }

  // ── Play next in queue ──
  async function playNext(guildId) {
    const state = getMusicState(guildId);
    if (state.ytProcess) { try { state.ytProcess.kill(); } catch {} state.ytProcess = null; }

    let track = null;
    if (state.loop && state.nowPlaying) {
      track = state.nowPlaying;
    } else if (state.queue.length > 0) {
      if (state.shuffle) {
        const idx = Math.floor(Math.random() * state.queue.length);
        track = state.queue.splice(idx, 1)[0];
      } else {
        track = state.queue.shift();
      }
      if (state.loopAll && state.nowPlaying) {
        state.queue.push(state.nowPlaying);
      }
    } else {
      // Queue empty — fire autoplay if enabled
      if (guildAutoplay.get(guildId) && state.nowPlaying?.videoId) {
        const prev = state.nowPlaying;
        state.nowPlaying = null;
        try {
          const related = await resolveYtSearch(
            `${prev.artist ? prev.artist + ' ' : ''}${prev.title} music`,
            prev.title, prev.artist
          );
          if (related.videoId && related.videoId !== prev.videoId) {
            state.queue.push({
              videoId: related.videoId, title: related.title, name: related.title,
              artist: related.artist, requestedBy: 'Autoplay',
              artwork: `https://img.youtube.com/vi/${related.videoId}/mqdefault.jpg`
            });
            return playNext(guildId);
          }
        } catch {}
      }
      state.nowPlaying = null;
      state.paused = false;
      stopLyricStatus();
      return;
    }

    state.nowPlaying = track;
    state.paused = false;
    state.trackStartedAt = Date.now();
    if (process.env.BOT_LYRICS_ENABLED !== '0') {
      startLyricStatus(guildId, track);
    } else {
      stopLyricStatus();
      if (_trackChangeCb) { try { _trackChangeCb(guildId, track); } catch {} }
    }

    try {
      if (!state.connection) return;
      const isFile = track.type === 'file' && track.filePath;
      const seekSecs = state.seekSeconds || 0;
      state.seekSeconds = null;
      state.trackSeekBase = seekSecs;
      const filterStr = _buildFilterStr(state.filters);
      const proc = isFile
        ? createFileStreamEx(track.filePath, seekSecs, filterStr)
        : createYtdlpStreamEx(track.videoId, seekSecs, filterStr);
      state.ytProcess = proc;
      // Both branches now emit s16le 48kHz stereo PCM, so StreamType.Raw is correct
      // for both. This bypasses discord.js's auto-detect path which was occasionally
      // causing wrong-speed playback when source sample rate != 48kHz.
      const resource = createAudioResource(proc.stdout, { inputType: StreamType.Raw, inlineVolume: true });
      resource.volume.setVolume(Math.max(0, Math.min(1, state.volume)));

      if (!state.player) {
        state.player = createAudioPlayer();
        state.connection.subscribe(state.player);
      }

      state.player.removeAllListeners(AudioPlayerStatus.Idle);
      state.player.removeAllListeners('error');
      state.player.on(AudioPlayerStatus.Idle, () => { playNext(guildId); });
      const trackTag = isFile ? track.filePath : track.videoId;
      state.player.on('error', (e) => {
        vlog(`[Music] Player error guild=${guildId} track=${trackTag}:`, e.message, e.resource?.metadata ? JSON.stringify(e.resource.metadata) : '');
        playNext(guildId);
      });
      let stderrBuf = '';
      proc.stderr.on('data', (chunk) => {
        stderrBuf += chunk.toString();
        if (stderrBuf.length > 4000) stderrBuf = stderrBuf.slice(-4000);
      });
      proc.on('exit', (code, sig) => {
        if (code && code !== 0) vlog(`[Music] ${isFile ? 'ffmpeg' : 'yt-dlp'} exited guild=${guildId} code=${code} sig=${sig} track=${trackTag}\n${stderrBuf.slice(-1500)}`);
      });
      proc.on('error', (err) => vlog(`[Music] ${isFile ? 'ffmpeg' : 'yt-dlp'} spawn error guild=${guildId}:`, err.message));
      state.player.play(resource);
      _onTrackChange(guildId, track);
      updateNowPlaying(guildId, track);
    } catch (e) {
      console.warn(`[Music] playNext error in ${guildId}:`, e.message);
      playNext(guildId);
    }
  }

  // ── Add to queue ──
  async function addToQueue(guildId, channelId, track, volume) {
    const state = getMusicState(guildId);
    if (volume != null) state.volume = volume;
    state.queue.push(track);

    if (state.nowPlaying) return true;

    try {
      if (state.connection) { try { state.connection.destroy(); } catch {} state.connection = null; state.player = null; }

      const connection = joinVoiceChannel({
        channelId, guildId,
        adapterCreator: createVoiceAdapter(guildId),
        selfDeaf: false,
        selfMute: false,
      });
      state.connection = connection;
      state.channelId = channelId;

      connection.on(VoiceConnectionStatus.Disconnected, async (oldS, newS) => {
        vlog(`[Voice] Disconnected guild=${guildId} reason=${newS?.reason ?? 'unknown'} closeCode=${newS?.closeCode ?? '-'} — attempting recovery`);
        try {
          await Promise.race([
            entersState(connection, VoiceConnectionStatus.Signalling, 5_000),
            entersState(connection, VoiceConnectionStatus.Connecting, 5_000),
          ]);
          vlog(`[Voice] Recovered guild=${guildId} (transient)`);
          return;
        } catch {}

        for (let attempt = 1; attempt <= 5; attempt++) {
          try {
            vlog(`[Voice] Rejoin attempt ${attempt} guild=${guildId}`);
            connection.rejoin();
            await entersState(connection, VoiceConnectionStatus.Ready, 15_000);
            vlog(`[Voice] Rejoined guild=${guildId} on attempt ${attempt}`);
            const s = getMusicState(guildId);
            if (!s.player) {
              s.player = createAudioPlayer();
              connection.subscribe(s.player);
            } else {
              connection.subscribe(s.player);
            }
            if (!s.nowPlaying && s.queue.length > 0) playNext(guildId);
            return;
          } catch (e) {
            vlog(`[Voice] Rejoin attempt ${attempt} failed guild=${guildId}: ${e.message}`);
            await new Promise(r => setTimeout(r, attempt * 2_000));
          }
        }

        vlog(`[Voice] All rejoin attempts failed guild=${guildId} — tearing down`);
        try { connection.destroy(); } catch {}
        const s = getMusicState(guildId);
        s.connection = null; s.player = null; s.nowPlaying = null; s.queue = [];
        if (_lyricOwner?.guildId === guildId) stopLyricStatus();
      });
      connection.on('error', (e) => vlog(`[Voice] Connection error guild=${guildId}: ${e.message}`));
      connection.on(VoiceConnectionStatus.Destroyed, () => vlog(`[Voice] Destroyed guild=${guildId}`));

      await entersState(connection, VoiceConnectionStatus.Ready, 20_000);
      await playNext(guildId);
      return true;
    } catch (e) {
      console.warn(`[Music] addToQueue connect error in ${guildId}:`, e.message);
      return false;
    }
  }

  // ── Music controls ──
  function skip(guildId) {
    const state = getMusicState(guildId);
    if (state.player) { state.loop = false; state.player.stop(); }
  }

  // Restart the currently-playing track from the beginning. Unshifts the track
  // to the front of the queue and nulls nowPlaying so the existing Idle->playNext
  // listener takes the dequeue path (skipping the per-track loop check, which
  // would otherwise loop on the same track without re-creating the resource).
  async function rewind(guildId) {
    const state = getMusicState(guildId);
    if (!state.nowPlaying) return false;
    const track = state.nowPlaying;
    state.queue.unshift(track);
    state.nowPlaying = null;
    if (state.player) state.player.stop();
    else await playNext(guildId);
    return true;
  }

  function pause(guildId) {
    const state = getMusicState(guildId);
    if (state.player) { state.player.pause(); state.paused = true; state.pausedAt = Date.now(); }
  }

  function resume(guildId) {
    const state = getMusicState(guildId);
    if (state.player) {
      if (state.pausedAt && state.trackStartedAt) { state.trackStartedAt += (Date.now() - state.pausedAt); }
      state.pausedAt = null;
      state.player.unpause();
      state.paused = false;
    }
  }

  function stop(guildId) {
    const state = getMusicState(guildId);
    state.queue = [];
    state.nowPlaying = null;
    state.loop = false;
    state.loopAll = false;
    if (state.ytProcess) { try { state.ytProcess.kill(); } catch {} state.ytProcess = null; }
    if (state.player) { state.player.removeAllListeners(); state.player.stop(); state.player = null; }
    if (state.connection) { try { state.connection.destroy(); } catch {} state.connection = null; }
    state.paused = false;
    if (_lyricOwner?.guildId === guildId) stopLyricStatus();
    const dt = dtState.get(guildId);
    if (dt) {
      if (dt.proc)   { try { dt.proc.kill();           } catch {} }
      if (dt.ff)     { try { dt.ff.kill();             } catch {} }
      if (dt.player) { try { dt.player.removeAllListeners(); dt.player.stop(); } catch {} }
      if (dt.conn)   { try { dt.conn.destroy();        } catch {} }
      dtState.delete(guildId);
    }
  }

  function setVolume(guildId, volume) {
    const state = getMusicState(guildId);
    state.volume = Math.max(0, Math.min(1, volume));
    if (state.player) {
      const res = state.player.state?.resource;
      if (res && res.volume) res.volume.setVolume(state.volume);
    }
  }

  function getStatus(guildId) {
    const state = getMusicState(guildId);
    // Surface upNext + progress + lyric-loading state so the in-app deploy UI
    // can render the same fields the Discord RPC card shows (see discord_rpc.py).
    const next = state.queue && state.queue[0];
    const upNext = next
      ? `${next.name || next.title || 'Unknown'}${next.artist ? ' - ' + next.artist : ''}`
      : null;
    let position = null, duration = null, lyricsReady = null;
    if (_lyricOwner && _lyricOwner.guildId === guildId) {
      position = Math.max(0, Math.floor((Date.now() - _lyricOwner.trackStart) / 1000));
      if (_lyricOwner.trackEnd) duration = Math.floor((_lyricOwner.trackEnd - _lyricOwner.trackStart) / 1000);
      lyricsReady = _lyricOwner.chunks.length > 0;
    }
    return {
      nowPlaying: state.nowPlaying,
      paused: state.paused,
      volume: state.volume,
      loop: state.loop,
      loopAll: state.loopAll,
      shuffle: state.shuffle,
      queueLength: state.queue.length,
      connected: !!state.connection,
      upNext, position, duration, lyricsReady
    };
  }

  function getQueue(guildId) { return getMusicState(guildId).queue; }
  function clearQueue(guildId) { getMusicState(guildId).queue = []; }

  function removeFromQueue(guildId, index) {
    const state = getMusicState(guildId);
    if (index >= 0 && index < state.queue.length) state.queue.splice(index, 1);
  }

  function shuffleQueue(guildId) {
    const state = getMusicState(guildId);
    for (let i = state.queue.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [state.queue[i], state.queue[j]] = [state.queue[j], state.queue[i]];
    }
  }

  function toggleLoop(guildId) {
    const state = getMusicState(guildId);
    state.loop = !state.loop;
    return state.loop;
  }

  function toggleLoopAll(guildId) {
    const state = getMusicState(guildId);
    state.loopAll = !state.loopAll;
    return state.loopAll;
  }

  // ── Direct voice (deploy feature) ──

  function stopVc(guildId) { stop(guildId); }

  async function joinAndPlay(guildId, channelId, videoId, volume = 0.2, trackMeta = {}) {
    stop(guildId);
    vlog(`[Voice] joinAndPlay guild=${guildId} channel=${channelId} botUser=${botUser?.id} ${trackMeta.filePath ? 'file='+trackMeta.filePath : 'videoId='+videoId}`);
    const track = trackMeta.filePath
      ? { filePath: trackMeta.filePath, name: trackMeta.name || trackMeta.filePath, artist: trackMeta.artist || '', artwork: trackMeta.artwork || null, type: 'file' }
      : { videoId, name: trackMeta.name || videoId, artist: trackMeta.artist || '', artwork: trackMeta.artwork || null, type: 'stream' };
    const ok = await addToQueue(guildId, channelId, track, volume);
    if (!ok) throw new Error('Failed to join voice channel. Check bot has Connect + Speak permissions.');
  }

  function _filterComponents(guildId) {
    const s = getMusicState(guildId);
    const f = s.filters || {};
    const bbOn = !!f.bassboost;
    return { type: 1, components: [
      { type: 2, style: bbOn            ? 3 : 2, label: bbOn ? `Bass: ${f.bassboost}` : 'Bass Boost', emoji: { name: '🎸' }, custom_id: `np_filter_bass_${guildId}` },
      { type: 2, style: f.chipmunk     ? 3 : 2, label: f.chipmunk  ? 'Chipmunk: ON'  : 'Chipmunk',  emoji: { name: '🐿️' }, custom_id: `np_filter_chipmunk_${guildId}` },
      { type: 2, style: f.vaporwave    ? 3 : 2, label: f.vaporwave  ? 'Vaporwave: ON'  : 'Vaporwave',  emoji: { name: '🌊' }, custom_id: `np_filter_vapor_${guildId}` },
      { type: 2, style: f['8d']        ? 3 : 2, label: f['8d']      ? '8D Audio: ON'  : '8D Audio',   emoji: { name: '🎧' }, custom_id: `np_filter_8d_${guildId}` },
      { type: 2, style: f.reverb       ? 3 : 2, label: f.reverb     ? 'Reverb: ON'    : 'Reverb',     emoji: { name: '🔁' }, custom_id: `np_filter_reverb_${guildId}` },
    ]};
  }

  function _buildNpEmbed(guildId, track) {
    const state = getMusicState(guildId);
    const qLen = state.queue.length;
    const httpArt = typeof track.artwork === 'string' && /^https?:\/\//i.test(track.artwork) ? track.artwork : null;
    const volPct = Math.round((state.volume || 0.5) * 100);
    const f = state.filters || {};
    const activeFilters = [
      f.bassboost  ? `🎸 Bass (${f.bassboost})` : null,
      f.chipmunk   ? '🐿️ Chipmunk' : null,
      f.vaporwave  ? '🌊 Vaporwave' : null,
      f.slowed     ? '🐌 Slowed' : null,
      f['8d']      ? '🎧 8D Audio' : null,
      f.reverb     ? '🔁 Reverb' : null,
      f.earrape    ? '💥 Earrape' : null,
    ].filter(Boolean);
    const statusBits = [
      `🔊 ${volPct}%`,
      state.loop    ? '🔂 Loop'     : null,
      state.loopAll ? '🔁 Loop All' : null,
      state.shuffle ? '🔀 Shuffle'  : null,
      state.locked  ? '🔒 Locked'   : null,
    ].filter(Boolean);
    const fields = [];
    if (qLen > 0) fields.push({ name: 'Up Next', value: `${qLen} track${qLen > 1 ? 's' : ''} in queue`, inline: true });
    if (activeFilters.length) fields.push({ name: 'Filters', value: activeFilters.join(' · '), inline: true });
    if (state.djRoleId) fields.push({ name: 'DJ Role', value: `<@&${state.djRoleId}>`, inline: true });
    return {
      color: 0x5865f2,
      author: { name: 'Now Playing' },
      title: track.name || track.title || 'Unknown Track',
      description: [track.artist, statusBits.join(' · ')].filter(Boolean).join('\n') || null,
      image: httpArt ? { url: httpArt } : null,
      fields,
      footer: { text: 'KawaiiPrinting — Row 1: transport · Row 2: loop/queue · Row 3: filters/DJ/volume' },
    };
  }

  function _npComponents(guildId) {
    const state = getMusicState(guildId);
    const looping    = !!state.loop;
    const loopingAll = !!state.loopAll;
    const locked     = !!state.locked;
    return [
      { type: 1, components: [
        { type: 2, style: 2,         label: 'Rewind',  emoji: { name: '⏮' }, custom_id: `np_rewind_${guildId}`  },
        { type: 2, style: 2,         label: 'Pause',   emoji: { name: '⏸' }, custom_id: `np_pause_${guildId}`   },
        { type: 2, style: 3,         label: 'Play',    emoji: { name: '▶' }, custom_id: `np_resume_${guildId}`  },
        { type: 2, style: 2,         label: 'Skip',    emoji: { name: '⏭' }, custom_id: `np_skip_${guildId}`    },
        { type: 2, style: 4,         label: 'Stop',    emoji: { name: '⏹' }, custom_id: `np_stop_${guildId}`    },
      ]},
      { type: 1, components: [
        { type: 2, style: looping    ? 3 : 2, label: 'Loop',     emoji: { name: '🔂' }, custom_id: `np_loop_${guildId}`    },
        { type: 2, style: loopingAll ? 3 : 2, label: 'Loop All', emoji: { name: '🔁' }, custom_id: `np_loopall_${guildId}` },
        { type: 2, style: 2,                  label: 'Shuffle',  emoji: { name: '🔀' }, custom_id: `np_shuffle_${guildId}` },
        { type: 2, style: 2,                  label: 'Add',      emoji: { name: '➕' }, custom_id: `np_add_${guildId}`     },
        { type: 2, style: 2,                  label: 'Queue',    emoji: { name: '📋' }, custom_id: `np_queue_${guildId}`   },
      ]},
      { type: 1, components: [
        { type: 2, style: 2,              label: 'Filters',              emoji: { name: '🎛️' }, custom_id: `np_filters_${guildId}` },
        { type: 2, style: locked ? 4 : 2, label: locked ? 'Locked' : 'Lock', emoji: { name: '🔒' }, custom_id: `np_lock_${guildId}` },
        { type: 2, style: 2,              label: 'Set DJ',               emoji: { name: '🎧' }, custom_id: `np_setdj_${guildId}`  },
        { type: 2, style: 2,              label: 'Vol −',                emoji: { name: '🔉' }, custom_id: `np_voldown_${guildId}` },
        { type: 2, style: 2,              label: 'Vol +',                emoji: { name: '🔊' }, custom_id: `np_volup_${guildId}`   },
      ]},
    ];
  }

  async function postNowPlaying(guildId, channelId, track) {
    const old = nowPlayingMsgs.get(guildId);
    if (old) { try { await rest('DELETE', `/channels/${old.channelId}/messages/${old.messageId}`, null, _token); } catch {} nowPlayingMsgs.delete(guildId); }
    const embed = _buildNpEmbed(guildId, track);
    const components = _npComponents(guildId);
    const res = await rest('POST', `/channels/${channelId}/messages`, { embeds: [embed], components }, _token);
    if (res.status === 200 || res.status === 201) nowPlayingMsgs.set(guildId, { channelId, messageId: res.data.id, track });
  }

  async function updateNowPlaying(guildId, track) {
    const np = nowPlayingMsgs.get(guildId);
    if (!np) return;
    np.track = track;
    const embed = _buildNpEmbed(guildId, track);
    const components = _npComponents(guildId);
    try { await rest('PATCH', `/channels/${np.channelId}/messages/${np.messageId}`, { embeds: [embed], components }, _token); } catch {}
  }

  function setVcVolume(guildId, volume) {
    const s = activeVoice.get(guildId);
    if (!s) return false;
    const v = Math.max(0, Math.min(1, volume));
    try { s.player?.state?.resource?.volume?.setVolume(v); } catch {}
    return true;
  }

  // ── Shared NSFW autopost lookup tables (all 37 content categories) ──
  const AP_CAT_QUERIES = {
    ass:'big ass booty close up', pussy:'wet dripping pussy close up', goth:'goth girl tattooed nude sex',
    thick:'thick curvy pawg nude', boobs:'big natural tits bouncing',
    hentai:'hentai anime sex uncensored', blowjob:'blowjob deepthroat sloppy', lesbian:'lesbian eating pussy orgasm',
    cum:'cumshot facial swallowing', feet:'sexy feet toes soles licking', thighs:'thick thighs spread stockings',
    nudes:'nude amateur girlfriend selfie', milf:'milf mature sex hardcore', ebony:'ebony black woman nude sex',
    asian:'asian petite nude sex', redhead:'redhead ginger nude sex', ahegao:'ahegao orgasm face',
    anal:'anal penetration gaping', bondage:'bondage tied bdsm sex', latina:'latina nude big ass sex',
    petite:'petite small girl nude sex', blonde:'blonde nude amateur sex', brunette:'brunette nude sex',
    bbw:'bbw chubby thick nude sex', trans:'trans girl nude sex', pov:'pov riding orgasm female',
    creampie:'creampie dripping pussy', squirt:'squirting orgasm gushing', titfuck:'titfuck cumshot tits',
    dp:'double penetration both holes', gangbang:'gangbang group sex', lingerie:'lingerie strip tease nude',
    cosplay:'cosplay nude sex', joi:'joi tease dirty talk nude', femdom:'femdom domination pegging',
    leggings:'tight leggings yoga pants spandex clothed',
    riding:'cowgirl riding cock orgasm', doggystyle:'doggystyle backshots fucking',
    handjob:'handjob cumshot stroking cock', outdoor:'outdoor public sex nude',
    massage:'massage sex happy ending nude', latex:'latex catsuit sex nude',
    facesitting:'facesitting pussy smother nude', rimjob:'rimjob ass licking analingus',
    'nsfw-gif':'hardcore sex gif amateur fucking', 'nsfw-video':'amateur sex video homemade couple',
  };
  const AP_CAT_SUBS = NSFW_CAT_SUBS;
  const AP_CAT_EMOJI = {
    ass:'🍑', pussy:'💧', blowjob:'👄', cum:'💦', lesbian:'🌸', hentai:'🎌', milf:'🔥',
    ebony:'⚡', anal:'🍆', feet:'👣', goth:'🖤', thick:'💪', boobs:'🍒',
    thighs:'🦵', nudes:'🔞', asian:'🌺', redhead:'🔴', ahegao:'👅', bondage:'⛓️',
    latina:'💃', petite:'🌸', blonde:'⭐', brunette:'🤎', bbw:'💜', trans:'🩵',
    pov:'👁️', creampie:'💦', squirt:'🌊', titfuck:'🍒', dp:'♾️', gangbang:'👥',
    lingerie:'👙', cosplay:'🎭', joi:'🫦', femdom:'👑', leggings:'🩱',
    riding:'🤠', doggystyle:'🔙', handjob:'✋', outdoor:'🌲',
    massage:'💆', latex:'⚫', facesitting:'😮', rimjob:'💋',
    'nsfw-gif':'🎞️', 'nsfw-video':'🎬',
  };
  const AP_CAT_COLORS = {
    ass:0xf5a623, pussy:0xff69b4, blowjob:0xff4081, cum:0xddeeff, lesbian:0xff80ab, hentai:0x7c4dff,
    milf:0xff5722, ebony:0x8d6e63, anal:0x9c27b0, feet:0x66bb6a, goth:0x2d2d2d, thick:0xe91e63,
    boobs:0xff6b6b, thighs:0xce93d8, nudes:0xffb74d, asian:0xff8f00, redhead:0xef5350,
    ahegao:0xf06292, bondage:0x37474f, latina:0xffa726, petite:0xec407a, blonde:0xffd54f,
    brunette:0xa1887f, bbw:0xba68c8, trans:0x4fc3f7, pov:0x4dd0e1, creampie:0x81d4fa,
    squirt:0x26c6da, titfuck:0xf48fb1, dp:0xff7043, gangbang:0xef9a9a, lingerie:0xf8bbd0,
    cosplay:0x7986cb, joi:0xf06292, femdom:0xad1457, leggings:0x66bb6a,
    riding:0xff8c00, doggystyle:0xe64a19, handjob:0xffa0a0, outdoor:0x4caf50,
    massage:0xff7043, latex:0x1a1a2e, facesitting:0xce93d8, rimjob:0xa5d6a7,
    'nsfw-gif':0xff6b35, 'nsfw-video':0xe53935,
  };
  // Required Redgifs tags per category — used by autopost to reject off-topic results.
  // fetchRedgifsContent accepts an optional requiredTags array; a result must have at least one matching tag.
  const AP_CAT_REQUIRED_TAGS = {
    ass:        ['ass','booty','butt','big ass','bigass','big butt'],
    pussy:      ['pussy','vagina','vulva'],
    goth:       ['goth','gothic','alternative','alt girl'],
    thick:      ['thick','pawg','curvy','chubby','thicc'],
    boobs:      ['boobs','tits','breasts','big tits','big boobs','natural tits'],
    hentai:     ['hentai','anime','cartoon','animated'],
    blowjob:    ['blowjob','bj','oral','deepthroat','sucking'],
    lesbian:    ['lesbian','girl on girl','girlongirl','two girls'],
    anal:       ['anal','anal sex','ass fuck','butt sex'],
    nudes:      ['nude','naked','strip','undress'],
    milf:       ['milf','mature','cougar'],
    asian:      ['asian','japanese','korean','chinese','thai'],
    redhead:    ['redhead','ginger'],
    feet:       ['feet','foot','toes','soles','foot fetish'],
    thighs:     ['thighs','legs','thigh'],
    ahegao:     ['ahegao','ahegoa'],
    bondage:    ['bondage','bdsm','tied','rope','restrained'],
    latina:     ['latina','latin'],
    petite:     ['petite','tiny','small','slim'],
    blonde:     ['blonde','blond'],
    brunette:   ['brunette'],
    bbw:        ['bbw','chubby','plus size','plussize','fat'],
    trans:      ['trans','transgender','shemale','tgirl'],
    pov:        ['pov','point of view'],
    creampie:   ['creampie','cream pie'],
    squirt:     ['squirt','squirting','gushing'],
    titfuck:    ['titfuck','paizuri','boobjob','tit job'],
    dp:         ['dp','double penetration','doublepenetration'],
    gangbang:   ['gangbang','group sex','orgy'],
    lingerie:   ['lingerie','bra','panties','underwear'],
    cosplay:    ['cosplay','costume','roleplay'],
    joi:        ['joi','jerk off instructions','dirty talk'],
    femdom:     ['femdom','female domination','dominatrix','mistress'],
    leggings:   ['leggings','yoga pants','spandex','tights','tight leggings','yoga'],
    riding:     ['riding','cowgirl','reverse cowgirl','girl on top'],
    doggystyle: ['doggystyle','doggy','doggy style','backshots'],
    handjob:    ['handjob','hand job','stroking','tugjob'],
    outdoor:    ['outdoor','public','outside'],
    massage:    ['massage','massage sex'],
    latex:      ['latex','rubber','pvc'],
    facesitting:['facesitting','face sitting','queening','smothering'],
    rimjob:     ['rimjob','rim job','analingus','ass licking'],
  };

  // ── Autocomplete handler (type 4) ──
  async function handleAutocomplete(d, token) {
    const cmd   = d.data?.name;
    const focused = d.data?.options?.find(o => o.focused);
    if (!focused) return;

    const CAT_FIELDS = ['category', 'category2', 'category3', 'category4'];
    if (cmd === 'nsfw-autopost' && CAT_FIELDS.includes(focused.name)) {
      const ALL_CATS = Object.keys(AP_CAT_QUERIES);

      // Discord caps autocomplete at 25. With 46 categories that means no single field can
      // show everything. Fix: split into two fixed halves so ALL categories are visible with
      // zero typing — field 1 shows page 1 (24 cats), field 2 shows page 2 (22 cats).
      // Fields 3 & 4 show whatever hasn't been picked yet (for stacking more picks).
      const PAGE1 = [
        'ass','pussy','boobs','blowjob','riding','doggystyle','cum','anal',
        'milf','lesbian','nudes','pov','creampie','squirt','thick','ebony',
        'asian','latina','blonde','brunette','petite','redhead','goth','trans',
      ]; // 24 entries — fills the slot perfectly alongside 🎲 random
      const PAGE2 = [
        'bbw','feet','thighs','lingerie','femdom','bondage','joi','gangbang',
        'titfuck','dp','ahegao','hentai','facesitting','cosplay','rimjob',
        'handjob','outdoor','massage','latex','leggings','nsfw-gif','nsfw-video',
      ]; // 22 entries — all remaining cats

      // Collect what's already chosen in the other three fields
      const otherPicked = CAT_FIELDS
        .filter(f => f !== focused.name)
        .map(f => (d.data?.options?.find(o => o.name === f)?.value || '').toLowerCase().trim())
        .filter(v => v && (ALL_CATS.includes(v) || v === 'random'));

      const partial = (focused.value || '').toLowerCase().trim();

      // When the user is typing, search across ALL cats with substring match
      if (partial) {
        const matched = ALL_CATS
          .filter(c => !otherPicked.includes(c) && c.includes(partial))
          .slice(0, 25)
          .map(c => ({ name: `${AP_CAT_EMOJI[c] || '🔞'} ${c}`, value: c }));
        await rest('POST', `/interactions/${d.id}/${d.token}/callback`,
          { type: 8, data: { choices: matched } }, token);
        return;
      }

      // No typing — show fixed page for this field so every category is visible somewhere
      let pool;
      if (focused.name === 'category') {
        pool = [{ name: `🎲 random — rotates all ${ALL_CATS.length} categories`, value: 'random' },
          ...PAGE1.filter(c => !otherPicked.includes(c)).map(c => ({ name: `${AP_CAT_EMOJI[c] || '🔞'} ${c}`, value: c }))];
      } else if (focused.name === 'category2') {
        pool = PAGE2.filter(c => !otherPicked.includes(c)).map(c => ({ name: `${AP_CAT_EMOJI[c] || '🔞'} ${c}`, value: c }));
      } else {
        // Fields 3 & 4: show everything not yet picked (any leftovers)
        pool = ALL_CATS
          .filter(c => !otherPicked.includes(c))
          .slice(0, 25)
          .map(c => ({ name: `${AP_CAT_EMOJI[c] || '🔞'} ${c}`, value: c }));
      }

      await rest('POST', `/interactions/${d.id}/${d.token}/callback`,
        { type: 8, data: { choices: pool.slice(0, 25) } }, token);
    }
  }

  // ── Command handler ──
  async function handleCommand(interaction, token) {
    const cmd = interaction.data?.name;
    const guildId = interaction.guild_id;
    const channelId = interaction.channel_id;
    const caller = interaction.member?.user || interaction.user || {};

    // Deferred response helpers — use when async work might exceed 3 s
    const deferReply = (ephemeral = false) =>
      rest('POST', `/interactions/${interaction.id}/${interaction.token}/callback`,
        { type: 5, data: { flags: ephemeral ? 64 : 0 } }, token);
    const editReply = (content, embeds) => {
      const data = (content !== null && typeof content === 'object' && !Array.isArray(content))
        ? content : { content: String(content), ...(embeds ? { embeds } : {}) };
      return rest('PATCH', `/webhooks/${botUser?.id}/${interaction.token}/messages/@original`, data, token);
    };
    // Deletes the public "thinking" placeholder then sends an ephemeral message only the invoking user can see.
    const ephemeralError = async (msg) => {
      await rest('DELETE', `/webhooks/${botUser?.id}/${interaction.token}/messages/@original`, null, token).catch(() => {});
      await rest('POST', `/webhooks/${botUser?.id}/${interaction.token}`, { content: msg, flags: 64 }, token).catch(() => {});
    };

    // Moderation guard: prevents acting on owner or members whose highest role >= bot's highest role
    async function canModerate(targetId) {
      const [gRes, rolesRes, botMem, targetMem] = await Promise.all([
        rest('GET', `/guilds/${guildId}`, null, token).catch(() => ({ data: {} })),
        rest('GET', `/guilds/${guildId}/roles`, null, token).catch(() => ({ data: [] })),
        rest('GET', `/guilds/${guildId}/members/${botUser?.id}`, null, token).catch(() => ({ data: {} })),
        rest('GET', `/guilds/${guildId}/members/${targetId}`, null, token).catch(() => ({ data: {} })),
      ]);
      if (targetId === gRes.data?.owner_id)
        return { ok: false, reason: '✗ Moderation commands cannot be used on the server owner.' };
      if (!targetMem.data?.user)
        return { ok: false, reason: '✗ Could not find that member in this server.' };
      const rolePos = Object.fromEntries((rolesRes.data || []).map(r => [r.id, r.position]));
      const botTop    = Math.max(0, ...(botMem.data?.roles    || []).map(id => rolePos[id] || 0));
      const targetTop = Math.max(0, ...(targetMem.data?.roles || []).map(id => rolePos[id] || 0));
      if (targetTop >= botTop)
        return { ok: false, reason: `✗ I cannot moderate <@${targetId}> — their highest role is equal to or above mine.` };
      return { ok: true };
    }

    // Permission guard for mod/admin commands: ADMINISTRATOR bit or a trusted mod role
    function hasModPermission() {
      const callerPerms = BigInt(interaction.member?.permissions || '0');
      if ((callerPerms & 8n) === 8n) return true;
      const callerRoles = interaction.member?.roles || [];
      const modRoles = guildModRoles.get(guildId) || new Set();
      return callerRoles.some(r => modRoles.has(r));
    }
    const MOD_DENIED = '❌ This command requires **Administrator** permission or a trusted mod role. Ask a server admin to run `/setmodrole` first.';

    try {
      switch (cmd) {
        case 'ping': {
          const t = Date.now() - startTime;
          await reply(interaction, token, `Pong! Bot has been online for **${msToTime(t)}**.`);
          break;
        }
        case 'uptime': {
          await reply(interaction, token, `I've been running for **${msToTime(Date.now() - startTime)}** without a restart.`);
          break;
        }
        case 'help': {
          const [gCmds, glCmds] = await Promise.all([
            rest('GET', `/applications/${botUser?.id}/guilds/${guildId}/commands`, null, token),
            rest('GET', `/applications/${botUser?.id}/commands`, null, token)
          ]);
          const _seen = new Set();
          const allCmds = [
            ...(gCmds.status === 200 && Array.isArray(gCmds.data) ? gCmds.data : []),
            ...(glCmds.status === 200 && Array.isArray(glCmds.data) ? glCmds.data : [])
          ].filter(c => { if (_seen.has(c.name)) return false; _seen.add(c.name); return true; });
          if (!allCmds.length) {
            await replyEmbed(interaction, token, {
              title: '📋 No Commands Registered',
              description: 'No slash commands are registered yet.\nOpen the app and go to **Bot Commands** to register commands.',
              color: 0xed4245
            });
            break;
          }
          // Group by category (Discord doesn't store category, so use name prefix heuristics)
          const catMap = {
            music:['play','skip','pause','resume','stop','queue','nowplaying','volume','shuffle','loop','seek','lyrics','playlist','remove','move','bassboost','nightcore','vaporwave','autoplay','save'],
            moderation:['warn','mute','unmute','kick','ban','unban','clear','slowmode','lock','unlock','nick','warnings','nuke'],
            fun:['coinflip','8ball','roll','rps','joke','meme','fact','quote','trivia','ascii','mock','reverse','rate','ship','roast','compliment','would-you-rather','truth-or-dare'],
            roleplay:['hug','pat','kiss','cuddle','slap','poke','tickle','bite','wave','cry','dance','wink','blush','highfive','shrug','lick'],
            utility:['ping','uptime','help','invite','avatar','embed','poll','timer','remind','translate','calc','color','base64','timestamp','qr','shorten'],
            info:['serverinfo','userinfo','botstats','membercount','roleinfo','channelinfo','permissions','firstmessage','emotes'],
            automation:['autorole','welcome','goodbye','reactionrole','reactionrole-add','starboard','autodelete','schedule','announce'],
          };
          const groups = {};
          for (const c of allCmds) {
            let cat = 'other';
            for (const [k, names] of Object.entries(catMap)) {
              if (names.includes(c.name)) { cat = k; break; }
            }
            if (!groups[cat]) groups[cat] = [];
            groups[cat].push({ name: c.name, desc: c.description });
          }
          const catEmojis = { music:'🎵', moderation:'🔨', fun:'🎉', roleplay:'💞', utility:'🔧', info:'ℹ️', automation:'⚙️', other:'📌' };
          const catColors = { music:0xf472b6, moderation:0xf87171, fun:0xa78bfa, roleplay:0xfb7185, utility:0x38bdf8, info:0x4ade80, automation:0x34d399, other:0x818cf8 };
          const pages = Object.entries(groups).map(([cat, cmds]) => ({
            title: `${catEmojis[cat] || '📌'} ${cat.charAt(0).toUpperCase() + cat.slice(1)} Commands`,
            description: cmds.map(c => `**/${c.name}** — ${c.desc}`).join('\n'),
            color: catColors[cat] || 0x5865f2,
            footer: { text: `Page {page} of {total} • ${allCmds.length} total commands` }
          }));
          const totalPages = pages.length;
          // Store pages in memory for button navigation
          const helpSessionId = `help_${interaction.id}`;
          helpSessions.set(helpSessionId, { pages, page: 0, userId: caller.id });
          setTimeout(() => helpSessions.delete(helpSessionId), 5 * 60 * 1000);
          const pg = pages[0];
          const embed = {
            title: pg.title,
            description: pg.description,
            color: pg.color,
            footer: { text: pg.footer.text.replace('{page}', '1').replace('{total}', totalPages) }
          };
          const components = totalPages > 1 ? [{
            type: 1,
            components: [
              { type: 2, style: 2, label: '◀ Previous', custom_id: `help_prev:${helpSessionId}`, disabled: true },
              { type: 2, style: 2, label: 'Next ▶', custom_id: `help_next:${helpSessionId}`, disabled: totalPages <= 1 }
            ]
          }] : [];
          await rest('POST', `/interactions/${interaction.id}/${interaction.token}/callback`,
            { type: 4, data: { embeds: [embed], components } }, token);
          break;
        }
        case 'invite': {
          const appId = botUser?.id || 'YOUR_CLIENT_ID';
          const inviteUrl = `https://discord.com/oauth2/authorize?client_id=${appId}&scope=bot+applications.commands&permissions=8`;
          await reply(interaction, token, `**Invite me to your server:**\n${inviteUrl}`);
          break;
        }
        case 'serverinfo': {
          const [gRes, chRes, memRes] = await Promise.all([
            rest('GET', `/guilds/${guildId}?with_counts=true`, null, token),
            rest('GET', `/guilds/${guildId}/channels`, null, token),
            rest('GET', `/guilds/${guildId}/members?limit=1000`, null, token),
          ]);
          if (gRes.status !== 200) { await reply(interaction, token, 'Could not fetch server info.', true); break; }
          const gd = gRes.data;
          const allCh  = Array.isArray(chRes.data)  ? chRes.data  : [];
          const allMem = Array.isArray(memRes.data) ? memRes.data : [];
          const approxTotal = gd.approximate_member_count || allMem.length;
          const isLarge = approxTotal > allMem.length;
          const humanCount = allMem.filter(m => !m.user?.bot).length;
          const botCount   = allMem.filter(m =>  m.user?.bot).length;
          const textCh  = allCh.filter(c => c.type === 0 || c.type === 5).length;
          const voiceCh = allCh.filter(c => c.type === 2 || c.type === 13).length;
          const totalCh = allCh.length;
          await replyEmbed(interaction, token, {
            title: gd.name, color: 0x5865f2,
            thumbnail: gd.icon ? { url: `https://cdn.discordapp.com/icons/${gd.id}/${gd.icon}.png` } : undefined,
            fields: [
              { name: 'Owner',       value: `<@${gd.owner_id}>`, inline: true },
              { name: 'Created',     value: `<t:${Math.floor(Number(BigInt(gd.id) >> 22n) / 1000 + 1420070400)}:R>`, inline: true },
              { name: 'Boost Level', value: `${gd.premium_tier}`, inline: true },
              { name: 'Members',     value: isLarge ? `~${approxTotal}` : `${humanCount}`, inline: true },
              { name: 'Bots',        value: isLarge ? '—' : `${botCount}`, inline: true },
              { name: 'Roles',       value: `${gd.roles?.length || '?'}`, inline: true },
              { name: 'Channels',    value: `${totalCh} total`, inline: true },
              { name: '# Text',      value: `${textCh}`, inline: true },
              { name: '🔊 Voice',    value: `${voiceCh}`, inline: true },
            ],
            footer: isLarge ? { text: `Large server — member/bot split not available for >1000 members` } : undefined,
          });
          break;
        }
        case 'userinfo': {
          const targetId = getOpt(interaction, 'user') || caller.id;
          const u = await rest('GET', `/guilds/${guildId}/members/${targetId}`, null, token);
          const ud = u.status === 200 ? u.data : null;
          const user = ud?.user || caller;
          await replyEmbed(interaction, token, {
            title: `${user.username}`, color: 0x57f287,
            thumbnail: user.avatar ? { url: `https://cdn.discordapp.com/avatars/${user.id}/${user.avatar}.png` } : undefined,
            fields: [
              { name: 'ID', value: user.id, inline: true },
              { name: 'Bot', value: user.bot ? 'Yes' : 'No', inline: true },
              { name: 'Joined Server', value: ud?.joined_at ? `<t:${Math.floor(new Date(ud.joined_at).getTime()/1000)}:R>` : 'Unknown', inline: true },
              { name: 'Account Created', value: `<t:${Math.floor(Number(BigInt(user.id) >> 22n) / 1000 + 1420070400)}:R>`, inline: true },
              { name: 'Nickname', value: ud?.nick || 'None', inline: true },
              { name: 'Roles', value: (ud?.roles?.length || 0).toString(), inline: true }
            ]
          });
          break;
        }
        case 'botstats': {
          const buRes  = await rest('GET', '/users/@me', null, token).catch(() => ({ data: botUser || {} }));
          const bu     = buRes.data || botUser || {};
          const avatarExt = bu.avatar?.startsWith('a_') ? 'gif' : 'png';
          const avatarUrl = bu.avatar
            ? `https://cdn.discordapp.com/avatars/${bu.id}/${bu.avatar}.${avatarExt}?size=256`
            : null;
          const bannerUrl = bu.banner
            ? `https://cdn.discordapp.com/banners/${bu.id}/${bu.banner}.${bu.banner.startsWith('a_') ? 'gif' : 'png'}?size=600`
            : null;
          const statsEmbed = {
            author: avatarUrl ? { name: bu.username || 'Bot', icon_url: avatarUrl } : undefined,
            title: `@${bu.username || 'Bot'}`,
            color: 0xf55036,
            thumbnail: avatarUrl ? { url: avatarUrl } : undefined,
            image:     bannerUrl ? { url: bannerUrl } : undefined,
            fields: [
              { name: '⏱️ Uptime',   value: msToTime(Date.now() - startTime), inline: true },
              { name: '🆔 Bot ID',   value: `\`${bu.id || '?'}\``,            inline: true },
              { name: '🟢 Status',   value: 'Online',                          inline: true },
              { name: '🎵 Music',    value: '/play /queue /skip /volume /loop /seek /playlist /lyrics +more', inline: false },
              { name: '🛡️ Moderation', value: '/kick /ban /mute /warn /clear /lock /slowmode /nick +more',  inline: false },
              { name: '🎮 Fun',      value: '/8ball /roll /joke /rps /coinflip /meme /trivia +more',        inline: false },
              { name: '📊 Info',     value: '/serverinfo /userinfo /membercount /roleinfo /avatar +more',   inline: false },
              { name: '🤖 Utility', value: '/help /ping /embed /reminder /poll /qr /translate +more',      inline: false },
            ],
            footer: { text: 'Discord Server Creator — by KawaiiPrinting' },
            timestamp: new Date().toISOString(),
          };
          await replyEmbed(interaction, token, statsEmbed);
          break;
        }
        case 'membercount': {
          const [g2Res, m2Res] = await Promise.all([
            rest('GET', `/guilds/${guildId}?with_counts=true`, null, token),
            rest('GET', `/guilds/${guildId}/members?limit=1000`, null, token),
          ]);
          const gd2    = g2Res.data || {};
          const mem2   = Array.isArray(m2Res.data) ? m2Res.data : [];
          const total2 = gd2.approximate_member_count || mem2.length;
          const isLg2  = total2 > mem2.length;
          if (isLg2) {
            await reply(interaction, token, `👥 This server has approximately **${total2}** members.`);
          } else {
            const h = mem2.filter(m => !m.user?.bot).length;
            const b = mem2.filter(m =>  m.user?.bot).length;
            await reply(interaction, token, `👥 **${total2}** total — **${h}** members · **${b}** bots`);
          }
          break;
        }
        case 'coinflip': {
          const isHeads = Math.random() < 0.5;
          await replyEmbed(interaction, token, {
            title: isHeads ? '🪙 Heads!' : '🪙 Tails!',
            description: isHeads
              ? '```\n ╔════════╗\n ║   👑   ║\n ║  HEADS ║\n ╚════════╝\n```'
              : '```\n ╔════════╗\n ║   🦅   ║\n ║  TAILS ║\n ╚════════╝\n```',
            color: isHeads ? 0xffd700 : 0xadb5bd,
            footer: { text: isHeads ? '✨ Shiny side up!' : 'Tails never fails... or does it?' },
          });
          break;
        }
        case '8ball': {
          const q = getOpt(interaction, 'question') || '...';
          await reply(interaction, token, `**${q}**\n> ${EIGHTBALL[Math.floor(Math.random() * EIGHTBALL.length)]}`);
          break;
        }
        case 'roll': {
          const raw = (getOpt(interaction, 'dice') || getOpt(interaction, 'max') || '100').trim();
          const dice = raw.match(/^(\d+)d(\d+)([+-]\d+)?$/i);
          if (dice) {
            const count = Math.min(50, parseInt(dice[1], 10) || 1);
            const sides = Math.max(2, parseInt(dice[2], 10));
            const mod = parseInt(dice[3] || '0', 10);
            const rolls = Array.from({ length: count }, () => Math.floor(Math.random() * sides) + 1);
            const total = rolls.reduce((a, b) => a + b, 0) + mod;
            await reply(interaction, token, `<@${caller.id}> rolled \`${raw}\`: [${rolls.join(', ')}]${mod ? ` ${mod>=0?'+':''}${mod}` : ''} = **${total}**`);
          } else {
            const max = Math.max(2, parseInt(raw, 10) || 100);
            await reply(interaction, token, `<@${caller.id}> rolled **${Math.floor(Math.random() * max) + 1}** out of ${max}!`);
          }
          break;
        }
        case 'rps': {
          const choices = ['Rock', 'Paper', 'Scissors'];
          const RPS_EMOJI = { Rock: '🪨', Paper: '📄', Scissors: '✂️' };
          const playerRaw = getOpt(interaction, 'choice') || choices[Math.floor(Math.random() * 3)];
          const botRaw = choices[Math.floor(Math.random() * 3)];
          let outcomeText, color;
          if (playerRaw === botRaw) { outcomeText = "🤝 **It's a tie!**"; color = 0xfee75c; }
          else if (RPS_WIN[playerRaw] === botRaw) { outcomeText = '🏆 **You win!**'; color = 0x57f287; }
          else { outcomeText = '🤖 **I win!**'; color = 0xed4245; }
          const beatVerb = playerRaw === botRaw ? 'ties with' : (RPS_WIN[playerRaw] === botRaw ? 'beats' : 'loses to');
          await replyEmbed(interaction, token, {
            title: '🎮 Rock · Paper · Scissors',
            description: `## ${RPS_EMOJI[playerRaw]}  **vs**  ${RPS_EMOJI[botRaw]}\n**You chose:** ${playerRaw}  •  **Bot chose:** ${botRaw}\n\n${outcomeText}`,
            color,
            footer: { text: `${playerRaw} ${beatVerb} ${botRaw}` },
          });
          break;
        }
        case 'joke': {
          const jokeType = (getOpt(interaction, 'type') || 'any').toLowerCase();
          const PUN_JOKES = [
            "I'm reading a book about anti-gravity. It's impossible to put down.",
            "Time flies like an arrow. Fruit flies like a banana.",
            "I used to hate facial hair, but then it grew on me.",
            "I told my wife she was drawing her eyebrows too high. She looked surprised.",
            "I have a joke about construction, but I'm still working on it.",
            "What do you call a fish with no eyes? A fsh.",
            "Why did the bicycle fall over? Because it was two-tired.",
            "What's brown and sticky? A stick.",
          ];
          const DARK_JOKES = [
            "I have many jokes about unemployed people, but none of them work.",
            "My grief counselor died. He was so good at his job, I didn't care.",
            "The cemetery is so overcrowded. People are dying to get in.",
            "Why don't cannibals eat clowns? Because they taste funny.",
            "I asked the doctor how long I had to live. He said '10'. I asked '10 what?' He replied '9, 8, 7...'",
            "I told a joke about a broken pencil once. It was pointless.",
          ];
          if (jokeType === 'dad') {
            try {
              const r = await httpFetch('GET', 'https://icanhazdadjoke.com/', { 'Accept': 'text/plain' });
              const text = (r.raw || '').trim();
              await reply(interaction, token, text ? `👨 ${text}` : `👨 ${JOKES[Math.floor(Math.random() * JOKES.length)]}`);
            } catch { await reply(interaction, token, `👨 ${JOKES[Math.floor(Math.random() * JOKES.length)]}`); }
          } else if (jokeType === 'pun') {
            await reply(interaction, token, `🙃 ${PUN_JOKES[Math.floor(Math.random() * PUN_JOKES.length)]}`);
          } else if (jokeType === 'dark') {
            await reply(interaction, token, `🌑 ${DARK_JOKES[Math.floor(Math.random() * DARK_JOKES.length)]}`);
          } else {
            const all = [...JOKES, ...PUN_JOKES];
            await reply(interaction, token, all[Math.floor(Math.random() * all.length)]);
          }
          break;
        }
        case 'warn': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const targetId = getOpt(interaction, 'user');
          const reason = getOpt(interaction, 'reason') || 'No reason provided';
          if (!targetId) { await reply(interaction, token, '❌ You must specify a user.', true); break; }
          await deferReply(false);
          const wGuard = await canModerate(targetId);
          if (!wGuard.ok) { await editReply(wGuard.reason); break; }
          const wKey = `${guildId}:${targetId}`;
          const warns = warnLog.get(wKey) || [];
          warns.push(`${new Date().toLocaleDateString()} — ${reason} (by <@${caller.id}>)`);
          warnLog.set(wKey, warns);
          await editReply(`⚠️ <@${targetId}> has been warned (${warns.length} total).\n**Reason:** ${reason}`);
          // Fire-and-forget DM so it never blocks the response
          rest('POST', '/users/@me/channels', { recipient_id: targetId }, token)
            .then(dm => dm.status === 200 && rest('POST', `/channels/${dm.data.id}/messages`,
              { content: `⚠️ You were warned in this server.\n**Reason:** ${reason}\n**Total warnings:** ${warns.length}` }, token))
            .catch(() => {});
          break;
        }
        case 'mute': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const targetId = getOpt(interaction, 'user');
          const minutes = parseInt(getOpt(interaction, 'duration') || '10', 10);
          const reason = getOpt(interaction, 'reason') || 'No reason provided';
          if (!targetId) { await reply(interaction, token, '❌ You must specify a user.', true); break; }
          await deferReply(false);
          const muteGuard = await canModerate(targetId);
          if (!muteGuard.ok) { await editReply(muteGuard.reason); break; }
          const until = new Date(Date.now() + minutes * 60 * 1000).toISOString();
          const r = await rest('PATCH', `/guilds/${guildId}/members/${targetId}`,
            { communication_disabled_until: until }, token);
          if (r.status === 200) await editReply(`🔇 <@${targetId}> has been timed out for **${minutes} minute(s)**.\n**Reason:** ${reason}`);
          else await editReply(`✗ Could not mute: ${r.data?.message || 'Missing permissions'}`);
          break;
        }
        case 'kick': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const targetId = getOpt(interaction, 'user');
          const reason = getOpt(interaction, 'reason') || 'No reason provided';
          if (!targetId) { await reply(interaction, token, '❌ You must specify a user.', true); break; }
          await deferReply(false);
          const kickGuard = await canModerate(targetId);
          if (!kickGuard.ok) { await editReply(kickGuard.reason); break; }
          const r = await rest('DELETE', `/guilds/${guildId}/members/${targetId}`, null, token);
          if (r.status === 204) await editReply(`👢 <@${targetId}> has been kicked.\n**Reason:** ${reason}`);
          else await editReply(`✗ Could not kick: ${r.data?.message || 'Missing permissions'}`);
          break;
        }
        case 'ban': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const targetId = getOpt(interaction, 'user');
          const reason = getOpt(interaction, 'reason') || 'No reason provided';
          if (!targetId) { await reply(interaction, token, '❌ You must specify a user.', true); break; }
          await deferReply(false);
          const banGuard = await canModerate(targetId);
          if (!banGuard.ok) { await editReply(banGuard.reason); break; }
          const r = await rest('PUT', `/guilds/${guildId}/bans/${targetId}`,
            { delete_message_seconds: 86400, reason }, token);
          if (r.status === 204 || r.status === 200) await editReply(`🔨 <@${targetId}> has been banned.\n**Reason:** ${reason}`);
          else await editReply(`✗ Could not ban: ${r.data?.message || 'Missing permissions'}`);
          break;
        }
        case 'clear': {
          const amount = getOpt(interaction, 'amount');
          if (amount != null && !hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          if (amount != null) {
            const n = Math.min(100, Math.max(1, parseInt(amount, 10)));
            const msgs = await rest('GET', `/channels/${channelId}/messages?limit=${n}`, null, token);
            if (msgs.status !== 200 || !msgs.data.length) { await reply(interaction, token, 'Could not fetch messages.', true); break; }
            const ids = msgs.data.map(m => m.id);
            if (ids.length === 1) {
              await rest('DELETE', `/channels/${channelId}/messages/${ids[0]}`, null, token);
            } else {
              await rest('POST', `/channels/${channelId}/messages/bulk-delete`, { messages: ids }, token);
            }
            await reply(interaction, token, `Deleted **${ids.length}** message(s).`, true);
          } else {
            clearQueue(guildId);
            await reply(interaction, token, 'Queue cleared.');
          }
          break;
        }
        case 'hug':
        case 'pat':
        case 'kiss':
        case 'cuddle':
        case 'slap':
        case 'poke':
        case 'tickle':
        case 'bite':
        case 'wave':
        case 'cry':
        case 'dance':
        case 'wink':
        case 'blush':
        case 'highfive':
        case 'shrug':
        case 'lick': {
          const rpTarget = getOpt(interaction, 'user');
          const rpDescriptions = {
            hug: ['gives a warm hug to','hugs','wraps their arms around'],
            pat: ['gently pats','gives a headpat to','pats on the head'],
            kiss: ['gives a sweet kiss to','plants a kiss on','kisses'],
            cuddle: ['cuddles with','snuggles up to','curls up with'],
            slap: ['slaps','gives a light slap to','playfully slaps'],
            poke: ['pokes','nudges','playfully pokes'],
            tickle: ['tickles','playfully tickles','starts tickling'],
            bite: ['playfully bites','gives a little nibble to','nibbles on'],
            wave: ['waves at','waves hello to','greets'],
            cry: ['is crying','breaks down crying at','sheds tears for'],
            dance: ['dances with','does a little dance for','breaks it down with'],
            wink: ['winks at','gives a cheeky wink to','winks playfully at'],
            blush: ['blushes at','turns red because of','blushes around'],
            highfive: ['highfives','slaps hands with','gives a high five to'],
            shrug: ['shrugs at','gives a ¯\\_(ツ)_/¯ to','shrugs toward'],
            lick: ['licks','gives a lick to','cheekily licks'],
          };
          const rpEmojis = {
            hug:'🫂',pat:'👋',kiss:'💋',cuddle:'🥰',slap:'👋',poke:'👉',
            tickle:'😄',bite:'😬',wave:'👋',cry:'😢',dance:'💃',wink:'😉',
            blush:'😊',highfive:'🙌',shrug:'🤷',lick:'👅'
          };
          const descs = rpDescriptions[cmd] || ['does something to'];
          const desc = descs[Math.floor(Math.random() * descs.length)];
          const emoji = rpEmojis[cmd] || '✨';
          const callerMention = `<@${caller.id}>`;
          const targetMention = rpTarget ? `<@${rpTarget}>` : 'everyone';
          const gifUrl = await fetchTenorGif(`anime ${cmd}`);
          const embed = {
            description: `${emoji} **${callerMention}** ${desc} **${targetMention}**!`,
            color: 0xf472b6,
            image: gifUrl ? { url: gifUrl } : undefined
          };
          await replyEmbed(interaction, token, embed);
          break;
        }
        case 'play': {
          const song = getOpt(interaction, 'song') || getOpt(interaction, 'query');
          if (!song) { await reply(interaction, token, 'Please provide a song name or URL.', true); break; }
          const vcKey = `${guildId}:${caller.id}`;
          const userVc = memberVoiceStates.get(vcKey);
          if (!userVc) { await reply(interaction, token, 'You need to be in a voice channel first.', true); break; }
          await reply(interaction, token, `Searching for **${song}**...`);
          try {
            // Honor URLs literally so users can pin the exact track they want.
            const ytMatch = song.match(/(?:youtube\.com.*[?&]v=|youtu\.be\/)([a-zA-Z0-9_-]{11})/);
            const spMatch = song.match(/open\.spotify\.com\/(?:intl-\w+\/)?track\/([a-zA-Z0-9]+)/);
            let videoId, title, artist;
            if (ytMatch) {
              videoId = ytMatch[1];
              const meta = await new Promise(r => execFile(getBin('yt-dlp'),
                [`https://www.youtube.com/watch?v=${videoId}`, '--print', '%(title)s<<|>>%(uploader)s', '--no-warnings', '--quiet', '--skip-download'],
                { timeout: 15000, env: _kpEnv() }, (e, out) => r(e ? null : out.trim()))).catch(() => null);
              if (meta) { const [t, u] = meta.split('<<|>>'); title = t || song; artist = u || ''; }
              else { title = song; artist = ''; }
            } else if (spMatch) {
              const sp = await resolveSpotifyTrack(song);
              const r = await resolveYtSearch(`${sp.title} ${sp.artist}`.trim(), sp.title, sp.artist, sp.durationMs);
              videoId = r.videoId; title = sp.title; artist = sp.artist;
            } else {
              const r = await resolveYtSearch(song);
              videoId = r.videoId; title = r.title; artist = r.artist;
            }
            const track = {
              title, artist, name: title,
              artwork: `https://img.youtube.com/vi/${videoId}/mqdefault.jpg`,
              videoId, query: song,
              requestedBy: caller.username || 'Unknown'
            };
            const vol = getMusicState(guildId).volume;
            await addToQueue(guildId, userVc, track, vol);
            const qPos = getMusicState(guildId).queue.length;
            const np = getMusicState(guildId).nowPlaying;
            const isPlaying = !!np;
            await rest('PATCH', `/webhooks/${botUser?.id || ''}/${interaction.token}/messages/@original`, {
              content: '',
              embeds: [{
                title: isPlaying ? '📋 Added to Queue' : '🎵 Now Playing',
                description: `**${title}**${artist ? `\n${artist}` : ''}`,
                color: isPlaying ? 0x5865f2 : 0x1db954,
                thumbnail: { url: `https://img.youtube.com/vi/${videoId}/mqdefault.jpg` },
                fields: isPlaying ? [{ name: 'Position in Queue', value: `#${qPos}`, inline: true }] : [],
                footer: { text: `Requested by ${caller.username || 'Unknown'}` }
              }],
              components: [{
                type: 1,
                components: [
                  { type: 2, style: 2, label: '⏸ Pause', custom_id: `music_pause:${guildId}` },
                  { type: 2, style: 2, label: '⏭ Skip', custom_id: `music_skip:${guildId}` },
                  { type: 2, style: 4, label: '⏹ Stop', custom_id: `music_stop:${guildId}` }
                ]
              }]
            }, token).catch(() => {});
          } catch (e) {
            await rest('PATCH', `/webhooks/${botUser?.id || ''}/${interaction.token}/messages/@original`,
              { content: `Could not find: ${e.message}` }, token).catch(() => {});
          }
          break;
        }
        case 'skip': {
          const state = getMusicState(guildId);
          if (!state.nowPlaying) { await reply(interaction, token, 'Nothing is playing.', true); break; }
          skip(guildId);
          await reply(interaction, token, 'Skipped.');
          break;
        }
        case 'pause': {
          const state = getMusicState(guildId);
          if (!state.nowPlaying) { await reply(interaction, token, 'Nothing is playing.', true); break; }
          pause(guildId);
          await reply(interaction, token, 'Paused.');
          break;
        }
        case 'resume': {
          const state = getMusicState(guildId);
          if (!state.nowPlaying) { await reply(interaction, token, 'Nothing is playing.', true); break; }
          resume(guildId);
          await reply(interaction, token, 'Resumed.');
          break;
        }
        case 'stop':
        case 'leave':
        case 'dc': {
          stop(guildId);
          await reply(interaction, token, 'Stopped and disconnected.');
          break;
        }
        case 'queue': {
          const state = getMusicState(guildId);
          const np = state.nowPlaying;
          if (!np && state.queue.length === 0) { await reply(interaction, token, 'The queue is empty.'); break; }
          let desc = '';
          if (np) desc += `**Now Playing:** ${np.title} - ${np.artist}\n\n`;
          if (state.queue.length > 0) {
            desc += '**Up Next:**\n';
            state.queue.slice(0, 10).forEach((t, i) => { desc += `${i + 1}. ${t.title} - ${t.artist}\n`; });
            if (state.queue.length > 10) desc += `...and ${state.queue.length - 10} more`;
          } else {
            desc += 'Queue is empty after current track.';
          }
          await replyEmbed(interaction, token, {
            title: 'Music Queue', description: desc, color: 0x1db954,
            footer: { text: `${state.queue.length} track(s) in queue` }
          });
          break;
        }
        case 'np': {
          const state = getMusicState(guildId);
          const track = state.nowPlaying;
          if (!track) { await reply(interaction, token, 'Nothing is playing right now.', true); break; }
          {
            const httpArt = typeof track.artwork === 'string' && /^https?:\/\//i.test(track.artwork) ? track.artwork : null;
            await replyEmbed(interaction, token, {
              title: 'Now Playing', description: `**${track.title}**\n${track.artist}`,
              thumbnail: httpArt ? { url: httpArt } : null, color: 0x1db954,
              footer: { text: `Requested by ${track.requestedBy} - Loop: ${state.loop} - Shuffle: ${state.shuffle}` }
            });
          }
          break;
        }
        case 'volume': {
          const level = parseInt(getOpt(interaction, 'level'), 10);
          if (isNaN(level) || level < 0 || level > 150) { await reply(interaction, token, 'Volume must be between 0 and 150.', true); break; }
          setVolume(guildId, level / 100);
          await reply(interaction, token, `Volume set to **${level}%**.`);
          break;
        }
        case 'shuffle': {
          const state = getMusicState(guildId);
          state.shuffle = !state.shuffle;
          await reply(interaction, token, `Shuffle is now **${state.shuffle ? 'on' : 'off'}**.`);
          break;
        }
        case 'loop': {
          const mode = (getOpt(interaction, 'mode') || '').toLowerCase();
          const state = getMusicState(guildId);
          if (mode === 'off')        { state.loop = false; state.loopAll = false; await reply(interaction, token, 'Loop is **off**.'); }
          else if (mode === 'track') { state.loop = true;  state.loopAll = false; await reply(interaction, token, 'Looping the **current track**.'); }
          else if (mode === 'queue') { state.loop = false; state.loopAll = true;  await reply(interaction, token, 'Looping the **whole queue**.'); }
          else {
            const s = toggleLoop(guildId);
            await reply(interaction, token, `Loop current track is now **${s ? 'on' : 'off'}**.`);
          }
          break;
        }
        case 'loopall': {
          const s = toggleLoopAll(guildId);
          await reply(interaction, token, `Loop queue is now **${s ? 'on' : 'off'}**.`);
          break;
        }
        case 'remove': {
          const pos = parseInt(getOpt(interaction, 'position'), 10);
          const state = getMusicState(guildId);
          if (isNaN(pos) || pos < 1 || pos > state.queue.length) {
            await reply(interaction, token, `Invalid position. Queue has ${state.queue.length} track(s).`, true); break;
          }
          const removed = state.queue[pos - 1];
          removeFromQueue(guildId, pos - 1);
          await reply(interaction, token, `Removed **${removed.title}** from the queue.`);
          break;
        }
        case 'move': {
          const from = parseInt(getOpt(interaction, 'from'), 10);
          const to = parseInt(getOpt(interaction, 'to'), 10);
          const state = getMusicState(guildId);
          const len = state.queue.length;
          if (isNaN(from) || isNaN(to) || from < 1 || from > len || to < 1 || to > len) {
            await reply(interaction, token, `Invalid positions. Queue has ${len} track(s).`, true); break;
          }
          const [item] = state.queue.splice(from - 1, 1);
          state.queue.splice(to - 1, 0, item);
          await reply(interaction, token, `Moved **${item.title}** from position ${from} to ${to}.`);
          break;
        }
        case 'nowplaying': {
          const s = getMusicState(guildId);
          const track = s.nowPlaying;
          if (!track) { await reply(interaction, token, 'Nothing is playing right now.', true); break; }
          {
            const httpArt = typeof track.artwork === 'string' && /^https?:\/\//i.test(track.artwork) ? track.artwork : null;
            await replyEmbed(interaction, token, {
              title: 'Now Playing', description: `**${track.name || track.title || 'Unknown'}**\n${track.artist || ''}`,
              thumbnail: httpArt ? { url: httpArt } : null, color: 0x5865f2
            });
          }
          break;
        }
        case 'lyrics': {
          const song = getOpt(interaction, 'song') || getOpt(interaction, 'query');
          const s = getMusicState(guildId);
          let title, artist;
          if (song) { title = song; artist = ''; }
          else if (s.nowPlaying) { title = s.nowPlaying.name || s.nowPlaying.title; artist = s.nowPlaying.artist || ''; }
          else { await reply(interaction, token, 'Nothing is playing and no song given.', true); break; }
          await rest('POST', `/interactions/${interaction.id}/${interaction.token}/callback`, { type: 5 }, token);
          const { plain, synced } = await fetchLyrics(title, artist);
          const text = plain || synced;
          const cleaned = text ? text.replace(/\[\d+:\d+\.\d+\]/g, '').trim().slice(0, 4000) : null;
          await rest('PATCH', `/webhooks/${botUser.id}/${interaction.token}/messages/@original`,
            { content: cleaned ? `**Lyrics — ${title}**\n\`\`\`\n${cleaned}\n\`\`\`` : 'No lyrics found.' }, token);
          break;
        }
        case 'seek': {
          const timeRaw = (getOpt(interaction, 'time') || '').trim();
          const state = getMusicState(guildId);
          if (!state.nowPlaying) { await reply(interaction, token, 'Nothing is playing.', true); break; }
          let secs = 0;
          const mm = timeRaw.match(/^(\d+):(\d+)$/);
          if (mm) secs = parseInt(mm[1]) * 60 + parseInt(mm[2]);
          else secs = Math.max(0, parseInt(timeRaw) || 0);
          state.seekSeconds = secs;
          const seekTrack = state.nowPlaying;
          state.queue.unshift(seekTrack);
          state.nowPlaying = null;
          if (state.player) state.player.stop(); else await playNext(guildId);
          await reply(interaction, token, `⏩ Seeked to **${Math.floor(secs/60)}:${String(secs%60).padStart(2,'0')}**.`);
          break;
        }
        case 'save': {
          const s = getMusicState(guildId);
          if (!s.nowPlaying) { await reply(interaction, token, 'Nothing is playing.', true); break; }
          const tr = s.nowPlaying;
          const ytUrl = tr.videoId ? `https://www.youtube.com/watch?v=${tr.videoId}` : (tr.url || null);
          try {
            const dm = await rest('POST', '/users/@me/channels', { recipient_id: caller.id }, token);
            if (!dm.data?.id) throw new Error('DM channel unavailable');
            await rest('POST', `/channels/${dm.data.id}/messages`, {
              content: `**💾 Saved Track**\n**${tr.title || tr.name || 'Unknown'}**${tr.artist ? ` — ${tr.artist}` : ''}${ytUrl ? `\n${ytUrl}` : ''}`
            }, token);
            await reply(interaction, token, '✅ Track saved to your DMs!', true);
          } catch { await reply(interaction, token, '❌ Could not DM you — make sure your DMs are open.', true); }
          break;
        }
        case 'bassboost': {
          const level = (getOpt(interaction, 'level') || '').toLowerCase();
          const state = getMusicState(guildId);
          if (level === 'off') {
            state.filters.bassboost = false;
          } else if (level === 'low' || level === 'medium' || level === 'high') {
            state.filters.bassboost = level;
          } else {
            state.filters.bassboost = state.filters.bassboost ? false : 'medium';
          }
          if (state.nowPlaying) { state.seekSeconds = _getPlaybackPos(state); state.queue.unshift(state.nowPlaying); state.nowPlaying=null; state.trackStartedAt=null; state.pausedAt=null; if(state.player)state.player.stop(); }
          const bbLabel = state.filters.bassboost ? `ON (${state.filters.bassboost})` : 'OFF';
          await reply(interaction, token, `🎸 Bass boost is now **${bbLabel}**.`);
          break;
        }
        case 'nightcore':
        case 'chipmunk': {
          const state = getMusicState(guildId);
          state.filters.chipmunk = !state.filters.chipmunk;
          if (state.filters.chipmunk) state.filters.vaporwave = state.filters.slowed = false;
          if (state.nowPlaying) { state.seekSeconds = _getPlaybackPos(state); state.queue.unshift(state.nowPlaying); state.nowPlaying=null; state.trackStartedAt=null; state.pausedAt=null; if(state.player)state.player.stop(); }
          await reply(interaction, token, `🐿️ Chipmunk is now **${state.filters.chipmunk ? 'ON' : 'OFF'}**.`);
          break;
        }
        case 'vaporwave': {
          const state = getMusicState(guildId);
          state.filters.vaporwave = !state.filters.vaporwave;
          if (state.filters.vaporwave) state.filters.chipmunk = state.filters.slowed = false;
          if (state.nowPlaying) { state.seekSeconds = _getPlaybackPos(state); state.queue.unshift(state.nowPlaying); state.nowPlaying=null; state.trackStartedAt=null; state.pausedAt=null; if(state.player)state.player.stop(); }
          await reply(interaction, token, `🌊 Vaporwave is now **${state.filters.vaporwave ? 'ON' : 'OFF'}**.`);
          break;
        }
        case 'slowed': {
          const state = getMusicState(guildId);
          state.filters.slowed = !state.filters.slowed;
          if (state.filters.slowed) state.filters.chipmunk = state.filters.vaporwave = false;
          if (state.nowPlaying) { state.seekSeconds = _getPlaybackPos(state); state.queue.unshift(state.nowPlaying); state.nowPlaying=null; state.trackStartedAt=null; state.pausedAt=null; if(state.player)state.player.stop(); }
          await reply(interaction, token, `🐌 Slowed is now **${state.filters.slowed ? 'ON' : 'OFF'}**.`);
          break;
        }
        case '8d': {
          const state = getMusicState(guildId);
          state.filters['8d'] = !state.filters['8d'];
          if (state.nowPlaying) { state.seekSeconds = _getPlaybackPos(state); state.queue.unshift(state.nowPlaying); state.nowPlaying=null; state.trackStartedAt=null; state.pausedAt=null; if(state.player)state.player.stop(); }
          await reply(interaction, token, `🎧 8D Audio is now **${state.filters['8d'] ? 'ON' : 'OFF'}**.`);
          break;
        }
        case 'reverb': {
          const state = getMusicState(guildId);
          state.filters.reverb = !state.filters.reverb;
          if (state.nowPlaying) { state.seekSeconds = _getPlaybackPos(state); state.queue.unshift(state.nowPlaying); state.nowPlaying=null; state.trackStartedAt=null; state.pausedAt=null; if(state.player)state.player.stop(); }
          await reply(interaction, token, `🔁 Reverb is now **${state.filters.reverb ? 'ON' : 'OFF'}**.`);
          break;
        }
        case 'autoplay': {
          const cur = guildAutoplay.get(guildId) || false;
          guildAutoplay.set(guildId, !cur);
          await reply(interaction, token, `🔄 Autoplay is now **${!cur ? 'ON' : 'OFF'}**.`);
          break;
        }
        case 'playlist': {
          const plUrl = getOpt(interaction, 'url') || '';
          const vcKey = `${guildId}:${caller.id}`;
          const userVc = memberVoiceStates.get(vcKey);
          if (!userVc) { await reply(interaction, token, 'You need to be in a voice channel first.', true); break; }
          await rest('POST', `/interactions/${interaction.id}/${interaction.token}/callback`, { type: 5 }, token);
          try {
            const plMatch = plUrl.match(/[?&]list=([^&]+)/);
            if (!plMatch) throw new Error('Only YouTube playlist URLs are supported. Make sure the URL contains `list=...`');
            const plId = plMatch[1];
            const metaOut = await new Promise(r => execFile(getBin('yt-dlp'),
              [`https://www.youtube.com/playlist?list=${plId}`, '--flat-playlist', '--print', '%(id)s<<|>>%(title)s<<|>>%(uploader)s', '--no-warnings', '--quiet'],
              { timeout: 30000, env: _kpEnv() }, (e, out) => r(e ? null : out.trim()))).catch(() => null);
            if (!metaOut) throw new Error('Could not fetch playlist — it may be private or invalid.');
            const tracks = metaOut.split('\n').filter(Boolean).slice(0, 50).map(line => {
              const [id, title, upl] = line.split('<<|>>');
              return { videoId: id, title: title || id, name: title || id, artist: upl || '', requestedBy: caller.username || 'Unknown', artwork: `https://img.youtube.com/vi/${id}/mqdefault.jpg` };
            });
            if (!tracks.length) throw new Error('No tracks found in playlist.');
            const state = getMusicState(guildId);
            if (state.nowPlaying || state.connection) {
              state.queue.push(...tracks);
            } else {
              state.queue.push(...tracks.slice(1));
              await addToQueue(guildId, userVc, tracks[0], state.volume);
            }
            await rest('PATCH', `/webhooks/${botUser?.id}/${interaction.token}/messages/@original`,
              { content: `✅ Added **${tracks.length}** tracks from playlist to queue.` }, token).catch(() => {});
          } catch (e) {
            await rest('PATCH', `/webhooks/${botUser?.id}/${interaction.token}/messages/@original`,
              { content: `❌ Playlist error: ${e.message}` }, token).catch(() => {});
          }
          break;
        }
        case 'unmute': {
          const targetId = getOpt(interaction, 'user');
          if (!targetId) { await reply(interaction, token, 'You must specify a user.', true); break; }
          const r = await rest('PATCH', `/guilds/${guildId}/members/${targetId}`,
            { communication_disabled_until: null }, token);
          if (r.status < 300) await reply(interaction, token, `<@${targetId}> has been unmuted.`);
          else await reply(interaction, token, `Could not unmute: ${r.data?.message || 'Missing permissions'}`, true);
          break;
        }
        case 'unban': {
          const uid = getOpt(interaction, 'userid');
          if (!uid) { await reply(interaction, token, 'User ID required.', true); break; }
          const r = await rest('DELETE', `/guilds/${guildId}/bans/${uid}`, null, token);
          if (r.status < 300) await reply(interaction, token, `User \`${uid}\` has been unbanned.`);
          else await reply(interaction, token, `Could not unban: ${r.data?.message || 'error'}`, true);
          break;
        }
        case 'slowmode': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const sec = parseInt(getOpt(interaction, 'seconds'), 10);
          if (isNaN(sec) || sec < 0 || sec > 21600) { await reply(interaction, token, 'Seconds must be 0-21600.', true); break; }
          const r = await rest('PATCH', `/channels/${channelId}`, { rate_limit_per_user: sec }, token);
          if (r.status < 300) await reply(interaction, token, sec ? `Slowmode set to **${sec}s**.` : 'Slowmode disabled.');
          else await reply(interaction, token, `Failed: ${r.data?.message || 'Missing permissions'}`, true);
          break;
        }
        case 'lock': case 'unlock': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const chanOpt = getOpt(interaction, 'channel') || channelId;
          const SEND = 1 << 11;
          const overwrite = cmd === 'lock'
            ? { id: guildId, type: 0, deny: String(SEND) }
            : { id: guildId, type: 0, deny: '0' };
          const r = await rest('PUT', `/channels/${chanOpt}/permissions/${guildId}`, overwrite, token);
          if (r.status < 300) await reply(interaction, token, cmd === 'lock' ? `<#${chanOpt}> locked.` : `<#${chanOpt}> unlocked.`);
          else await reply(interaction, token, `Failed: ${r.data?.message || 'Missing permissions'}`, true);
          break;
        }
        case 'nick': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const targetId = getOpt(interaction, 'user');
          const newNick = getOpt(interaction, 'nickname') ?? '';
          if (!targetId) { await reply(interaction, token, '❌ User required.', true); break; }
          await deferReply(false);
          const nickGuard = await canModerate(targetId);
          if (!nickGuard.ok) { await editReply(nickGuard.reason); break; }
          const r = await rest('PATCH', `/guilds/${guildId}/members/${targetId}`, { nick: newNick || null }, token);
          if (r.status < 300) await editReply(newNick ? `✏️ Nickname set to **${newNick}**.` : '✏️ Nickname cleared.');
          else await editReply(`✗ Failed: ${r.data?.message || 'Missing permissions'}`);
          break;
        }
        case 'avatar': {
          const targetId = getOpt(interaction, 'user') || caller.id;
          const ur = await rest('GET', `/users/${targetId}`, null, token);
          if (ur.status !== 200) { await reply(interaction, token, 'Could not fetch user.', true); break; }
          const u = ur.data;
          const ext = u.avatar?.startsWith('a_') ? 'gif' : 'png';
          const url = u.avatar
            ? `https://cdn.discordapp.com/avatars/${u.id}/${u.avatar}.${ext}?size=1024`
            : `https://cdn.discordapp.com/embed/avatars/${(parseInt(u.id) >> 22) % 6}.png`;
          await replyEmbed(interaction, token, { title: `${u.username}'s avatar`, image: { url }, color: 0x5865f2 });
          break;
        }
        case 'embed': {
          const title = getOpt(interaction, 'title') || '';
          const desc  = getOpt(interaction, 'description') || '';
          const image = getOpt(interaction, 'image');
          const thumb = getOpt(interaction, 'thumbnail');
          const colorInput = getOpt(interaction, 'color');
          const color = colorInput ? parseInt(colorInput.replace('#',''), 16) : 0x5865f2;
          const e = {
            title: title || undefined,
            description: desc || undefined,
            color: isNaN(color) ? 0x5865f2 : color,
            image: image && /^https?:\/\//.test(image) ? { url: image } : undefined,
            thumbnail: thumb && /^https?:\/\//.test(thumb) ? { url: thumb } : undefined
          };
          await replyEmbed(interaction, token, e);
          break;
        }
        case 'poll': {
          const q = getOpt(interaction, 'question');
          const optsRaw = getOpt(interaction, 'options') || '';
          const opts = optsRaw.split(/[,;|\n]+/).map(s => s.trim()).filter(Boolean).slice(0, 10);
          if (!q || opts.length < 2) { await reply(interaction, token, 'Provide a question and at least 2 options (comma-separated).', true); break; }
          const nums = ['1\uFE0F\u20E3','2\uFE0F\u20E3','3\uFE0F\u20E3','4\uFE0F\u20E3','5\uFE0F\u20E3','6\uFE0F\u20E3','7\uFE0F\u20E3','8\uFE0F\u20E3','9\uFE0F\u20E3','\uD83D\uDD1F'];
          const desc = opts.map((o, i) => `${nums[i]} ${o}`).join('\n');
          await replyEmbed(interaction, token, { title: q, description: desc, color: 0x5865f2, footer: { text: 'React below to vote' } });
          const msg = await rest('GET', `/webhooks/${botUser.id}/${interaction.token}/messages/@original`, null, token);
          if (msg.status === 200 && msg.data?.id) {
            for (let i = 0; i < opts.length; i++) {
              try { await rest('PUT', `/channels/${channelId}/messages/${msg.data.id}/reactions/${encodeURIComponent(nums[i])}/@me`, null, token); } catch {}
            }
          }
          break;
        }
        case 'timer': {
          const raw = (getOpt(interaction, 'duration') || getOpt(interaction, 'seconds') || '60').toString().trim();
          const m = raw.match(/^(\d+)\s*([smhd]?)$/i);
          let secs = 60;
          if (m) {
            const mult = { s: 1, m: 60, h: 3600, d: 86400 }[(m[2] || 's').toLowerCase()];
            secs = Math.max(1, Math.min(86400, parseInt(m[1], 10) * mult));
          } else {
            secs = Math.max(1, Math.min(86400, parseInt(raw, 10) || 60));
          }
          const msg = getOpt(interaction, 'message');
          await reply(interaction, token, `Timer started for **${secs}s**. I'll ping you when it's done.`);
          setTimeout(() => {
            const body = msg ? `<@${caller.id}> ${msg} (${secs}s timer up)` : `<@${caller.id}> Timer finished (${secs}s)!`;
            rest('POST', `/channels/${channelId}/messages`, { content: body }, token).catch(() => {});
          }, secs * 1000);
          break;
        }
        case 'remind': {
          const timeStr = getOpt(interaction, 'time') || '1h';
          const msg = getOpt(interaction, 'message') || 'Reminder';
          const m = timeStr.match(/^(\d+)\s*([smhd]?)$/i);
          if (!m) { await reply(interaction, token, 'Invalid time. Use e.g. `30s`, `15m`, `2h`, `1d`.', true); break; }
          const mult = { s: 1, m: 60, h: 3600, d: 86400 }[m[2].toLowerCase() || 's'];
          const secs = parseInt(m[1], 10) * mult;
          if (secs < 1 || secs > 60 * 60 * 24 * 7) { await reply(interaction, token, 'Time must be under 7 days.', true); break; }
          await reply(interaction, token, `I'll remind you in **${timeStr}**: ${msg}`);
          setTimeout(async () => {
            try {
              const dm = await rest('POST', `/users/@me/channels`, { recipient_id: caller.id }, token);
              if (dm.data?.id) await rest('POST', `/channels/${dm.data.id}/messages`, { content: `\u23F0 Reminder: ${msg}` }, token);
            } catch {}
          }, secs * 1000);
          break;
        }
        case 'translate': {
          const text = getOpt(interaction, 'text');
          const to = (getOpt(interaction, 'to') || 'en').toLowerCase();
          if (!text) { await reply(interaction, token, 'Text required.', true); break; }
          const url = `https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl=${encodeURIComponent(to)}&dt=t&q=${encodeURIComponent(text)}`;
          try {
            const r = await httpFetch('GET', url);
            const j = typeof r.data === 'string' ? JSON.parse(r.data) : r.data;
            const out = (j?.[0] || []).map(p => p[0]).join('');
            await reply(interaction, token, out ? `**${to}:** ${out}` : 'Translation failed.');
          } catch (e) { await reply(interaction, token, `Translate error: ${e.message}`, true); }
          break;
        }
        case 'calc': {
          const expr = getOpt(interaction, 'expression') || '';
          try {
            const v = safeMathEval(expr);
            await reply(interaction, token, `\`${expr}\` = **${v}**`);
          } catch (e) { await reply(interaction, token, `Bad expression: ${e.message}`, true); }
          break;
        }
        case 'color': {
          const v = (getOpt(interaction, 'value') || '').trim();
          let hex = null;
          if (/^#?[0-9a-f]{6}$/i.test(v)) hex = v.replace('#','').toLowerCase();
          else {
            const m = v.match(/rgb\s*\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)/i);
            if (m) hex = [m[1],m[2],m[3]].map(n => (+n).toString(16).padStart(2,'0')).join('');
            else {
              const named = { red:'ff0000', green:'00ff00', blue:'0000ff', white:'ffffff', black:'000000', yellow:'ffff00', cyan:'00ffff', magenta:'ff00ff', orange:'ffa500', purple:'800080', pink:'ffc0cb', gray:'808080', grey:'808080' };
              hex = named[v.toLowerCase()] || null;
            }
          }
          if (!hex) { await reply(interaction, token, 'Invalid color. Try `#ff5733`, `rgb(255,87,51)`, or a name.', true); break; }
          const intC = parseInt(hex, 16);
          await replyEmbed(interaction, token, {
            title: `#${hex}`,
            description: `RGB(${(intC>>16)&255}, ${(intC>>8)&255}, ${intC&255})`,
            color: intC,
            thumbnail: { url: `https://singlecolorimage.com/get/${hex}/200x200.png` }
          });
          break;
        }
        case 'base64': {
          const mode = getOpt(interaction, 'mode');
          const text = getOpt(interaction, 'text') || '';
          try {
            const out = mode === 'decode'
              ? Buffer.from(text, 'base64').toString('utf8')
              : Buffer.from(text, 'utf8').toString('base64');
            await reply(interaction, token, `\`\`\`\n${out.slice(0, 1900)}\n\`\`\``);
          } catch (e) { await reply(interaction, token, `Failed: ${e.message}`, true); }
          break;
        }
        case 'timestamp': {
          const dt = getOpt(interaction, 'datetime') || '';
          const style = getOpt(interaction, 'style') || 'f';
          let t = /^\d+$/.test(dt) ? parseInt(dt, 10) : Math.floor(new Date(dt).getTime() / 1000);
          if (isNaN(t) || !t) { await reply(interaction, token, 'Invalid date/time.', true); break; }
          await reply(interaction, token, `\`<t:${t}:${style}>\` -> <t:${t}:${style}>`);
          break;
        }
        case 'epoch': {
          const v = (getOpt(interaction, 'value') || '').trim();
          if (/^\d+$/.test(v)) {
            const n = parseInt(v, 10);
            const ts = n < 1e12 ? n * 1000 : n;
            await reply(interaction, token, `\`${v}\` -> ${new Date(ts).toISOString()}`);
          } else {
            const t = Math.floor(new Date(v).getTime() / 1000);
            if (isNaN(t)) { await reply(interaction, token, 'Invalid input.', true); break; }
            await reply(interaction, token, `\`${v}\` -> **${t}** (<t:${t}:F>)`);
          }
          break;
        }
        case 'qr': {
          const text = getOpt(interaction, 'text') || '';
          const url = `https://api.qrserver.com/v1/create-qr-code/?size=400x400&data=${encodeURIComponent(text)}`;
          await replyEmbed(interaction, token, { title: 'QR Code', image: { url }, color: 0x5865f2 });
          break;
        }
        case 'shorten': {
          const long = getOpt(interaction, 'url') || '';
          try {
            const r = await httpFetch('GET', `https://is.gd/create.php?format=simple&url=${encodeURIComponent(long)}`);
            const short = (r.raw || '').trim();
            if (!/^https?:\/\//.test(short)) throw new Error(short || 'Bad response');
            await reply(interaction, token, `<${long}> -> ${short}`);
          } catch (e) { await reply(interaction, token, `Shorten failed: ${e.message}`, true); }
          break;
        }
        case 'json': {
          const data = getOpt(interaction, 'data') || '';
          try {
            const parsed = JSON.parse(data);
            const pretty = JSON.stringify(parsed, null, 2).slice(0, 1900);
            await reply(interaction, token, `\`\`\`json\n${pretty}\n\`\`\``);
          } catch (e) { await reply(interaction, token, `Invalid JSON: ${e.message}`, true); }
          break;
        }
        case 'hash': {
          const text = getOpt(interaction, 'text') || '';
          const algo = getOpt(interaction, 'algo') || 'sha256';
          try {
            const out = require('crypto').createHash(algo).update(text).digest('hex');
            await reply(interaction, token, `**${algo.toUpperCase()}**: \`${out}\``);
          } catch (e) { await reply(interaction, token, `Hash failed: ${e.message}`, true); }
          break;
        }
        case 'regex': {
          const pattern = getOpt(interaction, 'pattern') || '';
          const text = getOpt(interaction, 'text') || '';
          try {
            const re = new RegExp(pattern, 'g');
            const matches = text.match(re) || [];
            await reply(interaction, token, matches.length
              ? `Found **${matches.length}** match(es): ${matches.slice(0, 20).map(m => `\`${m}\``).join(', ')}`
              : 'No matches found.');
          } catch (e) { await reply(interaction, token, `Bad regex: ${e.message}`, true); }
          break;
        }
        case 'ip': {
          const addr = getOpt(interaction, 'address') || '';
          try {
            const r = await httpFetch('GET', `http://ip-api.com/json/${encodeURIComponent(addr)}?fields=status,country,regionName,city,isp,org,query,lat,lon,timezone`);
            const d = typeof r.data === 'string' ? JSON.parse(r.data) : r.data;
            if (d.status !== 'success') throw new Error(d.message || 'lookup failed');
            await replyEmbed(interaction, token, {
              title: `IP Info — ${d.query}`, color: 0x38bdf8,
              fields: [
                { name: 'Country', value: d.country || '-', inline: true },
                { name: 'Region',  value: d.regionName || '-', inline: true },
                { name: 'City',    value: d.city || '-', inline: true },
                { name: 'ISP',     value: d.isp || '-', inline: true },
                { name: 'Org',     value: d.org || '-', inline: true },
                { name: 'Timezone',value: d.timezone || '-', inline: true },
                { name: 'Lat/Lon', value: `${d.lat}, ${d.lon}`, inline: true }
              ]
            });
          } catch (e) { await reply(interaction, token, `IP lookup failed: ${e.message}`, true); }
          break;
        }
        case 'dns': {
          const domain = getOpt(interaction, 'domain') || '';
          const type = getOpt(interaction, 'type') || 'A';
          try {
            const r = await httpFetch('GET', `https://cloudflare-dns.com/dns-query?name=${encodeURIComponent(domain)}&type=${type}`, { 'Accept': 'application/dns-json' });
            const d = typeof r.data === 'string' ? JSON.parse(r.data) : r.data;
            const ans = (d.Answer || []).map(a => `**${a.type}** ${a.data} (TTL ${a.TTL})`).join('\n').slice(0, 1800);
            await reply(interaction, token, ans ? `**${type} records for ${domain}:**\n${ans}` : `No ${type} records found.`);
          } catch (e) { await reply(interaction, token, `DNS error: ${e.message}`, true); }
          break;
        }
        case 'whois': {
          const domain = getOpt(interaction, 'domain') || '';
          try {
            const r = await httpFetch('GET', `https://rdap.org/domain/${encodeURIComponent(domain)}`);
            const d = typeof r.data === 'string' ? JSON.parse(r.data) : r.data;
            if (!d || d.errorCode) throw new Error(d?.title || 'not found');
            const events = (d.events || []).map(e => `${e.eventAction}: ${e.eventDate?.slice(0,10)}`).join('\n');
            const ns = (d.nameservers || []).map(n => n.ldhName).join(', ');
            await replyEmbed(interaction, token, {
              title: `WHOIS — ${d.ldhName || domain}`, color: 0x38bdf8,
              description: `**Status:** ${(d.status || []).join(', ') || '-'}\n**Nameservers:** ${ns || '-'}\n\n${events}`.slice(0, 4000)
            });
          } catch (e) { await reply(interaction, token, `WHOIS error: ${e.message}`, true); }
          break;
        }
        case 'headers': {
          const url = getOpt(interaction, 'url') || '';
          try {
            const r = await httpFetch('GET', url);
            const out = Object.entries(r.headers).slice(0, 20).map(([k, v]) => `**${k}:** ${v}`).join('\n').slice(0, 1800);
            await reply(interaction, token, `**Status:** ${r.status}\n${out}`);
          } catch (e) { await reply(interaction, token, `Fetch error: ${e.message}`, true); }
          break;
        }
        case 'statuscheck': {
          const url = getOpt(interaction, 'url') || '';
          try {
            const t0 = Date.now();
            const r = await httpFetch('GET', url);
            await reply(interaction, token, r.status < 400
              ? `\uD83D\uDFE2 **${url}** is up — ${r.status} in ${Date.now() - t0}ms`
              : `\uD83D\uDD34 **${url}** returned **${r.status}**`);
          } catch (e) { await reply(interaction, token, `\uD83D\uDD34 **${url}** is down: ${e.message}`); }
          break;
        }
        case 'scrape': {
          const url = getOpt(interaction, 'url') || '';
          try {
            const r = await httpFetch('GET', url);
            const html = r.raw || '';
            const pick = re => (html.match(re) || [])[1];
            const title = pick(/<title[^>]*>([^<]+)</i);
            const desc  = pick(/<meta[^>]+name=["']description["'][^>]+content=["']([^"']+)["']/i);
            const ogt   = pick(/<meta[^>]+property=["']og:title["'][^>]+content=["']([^"']+)["']/i);
            const ogd   = pick(/<meta[^>]+property=["']og:description["'][^>]+content=["']([^"']+)["']/i);
            const ogi   = pick(/<meta[^>]+property=["']og:image["'][^>]+content=["']([^"']+)["']/i);
            await replyEmbed(interaction, token, {
              title: (ogt || title || url).slice(0, 256), url,
              description: (ogd || desc || '').slice(0, 4000),
              thumbnail: ogi ? { url: ogi } : null, color: 0x5865f2
            });
          } catch (e) { await reply(interaction, token, `Scrape error: ${e.message}`, true); }
          break;
        }
        case 'pastebin': {
          const code = getOpt(interaction, 'code') || '';
          await deferReply(false);
          let pasted = false;
          // Try paste.rs first — POST raw content, returns plain URL
          try {
            const r1 = await httpFetch('POST', 'https://paste.rs/', { 'Content-Type': 'text/plain; charset=utf-8' }, code);
            const link1 = (r1.raw || '').trim();
            if (/^https?:\/\//.test(link1)) {
              await editReply({ embeds: [{ title: '📋 Paste Created', description: link1, color: 0x57f287, footer: { text: 'paste.rs' } }] });
              pasted = true;
            }
          } catch {}
          // Fallback: 0x0.st multipart
          if (!pasted) {
            try {
              const boundary = '----Form' + Date.now();
              const body = `--${boundary}\r\nContent-Disposition: form-data; name="file"; filename="paste.txt"\r\nContent-Type: text/plain\r\n\r\n${code}\r\n--${boundary}--\r\n`;
              const r2 = await httpFetch('POST', 'https://0x0.st/', { 'Content-Type': `multipart/form-data; boundary=${boundary}` }, body);
              const link2 = (r2.raw || '').trim();
              if (/^https?:\/\//.test(link2)) {
                await editReply({ embeds: [{ title: '📋 Paste Created', description: link2, color: 0x57f287, footer: { text: '0x0.st' } }] });
                pasted = true;
              }
            } catch {}
          }
          if (!pasted) await editReply('Could not create paste — both services unavailable.');
          break;
        }
        case 'screenshot': {
          const url = getOpt(interaction, 'url') || '';
          await deferReply(false);
          try {
            const apiUrl = `https://api.microlink.io/?url=${encodeURIComponent(url)}&screenshot=true&meta=false`;
            const r = await httpFetch('GET', apiUrl);
            const parsed = typeof r.data === 'string' ? JSON.parse(r.data) : r.data;
            const imgUrl = parsed?.data?.screenshot?.url;
            if (!imgUrl) throw new Error('screenshot service returned no image');
            await editReply({ embeds: [{ title: '📸 Screenshot', description: `[${url}](${url})`, image: { url: imgUrl }, color: 0x5865f2 }] });
          } catch (e) {
            // Fallback to thum.io
            const fallbackUrl = `https://image.thum.io/get/width/1280/crop/800/${url}`;
            await editReply({ embeds: [{ title: '📸 Screenshot', description: `[${url}](${url})`, image: { url: fallbackUrl }, color: 0x5865f2 }] });
          }
          break;
        }
        case 'ascii': {
          const text = (getOpt(interaction, 'text') || '').slice(0, 20);
          const art = renderAsciiArt(text);
          await reply(interaction, token, `\`\`\`\n${art}\n\`\`\``);
          break;
        }
        case 'mock': {
          const t = getOpt(interaction, 'text') || '';
          await reply(interaction, token, t.split('').map((c, i) => i % 2 ? c.toUpperCase() : c.toLowerCase()).join(''));
          break;
        }
        case 'reverse': {
          await reply(interaction, token, (getOpt(interaction, 'text') || '').split('').reverse().join(''));
          break;
        }
        case 'rate': {
          const thing = getOpt(interaction, 'thing') || '';
          // Check for image attachment option (command must define an ATTACHMENT option named "image")
          const rateImgId = (interaction.data?.options || []).find(o => o.name === 'image')?.value;
          const rateImg = rateImgId ? interaction.data?.resolved?.attachments?.[rateImgId] : null;
          // Check for user mention
          const rateMentionMatch = thing.match(/^<@!?(\d+)>$/);
          const rateSubject = rateImg ? 'that image' : thing || 'nothing';
          let rh = 0; for (let i = 0; i < rateSubject.length; i++) rh = ((rh << 5) - rh + rateSubject.charCodeAt(i)) | 0;
          const rateScore = Math.abs(rh) % 11;
          const rateBar = '█'.repeat(rateScore) + '░'.repeat(10 - rateScore);
          const rateColor = rateScore >= 8 ? 0x57f287 : rateScore >= 5 ? 0xfee75c : 0xed4245;
          if (rateImg) {
            await replyEmbed(interaction, token, {
              title: `${rateScore}/10`,
              description: `\`[${rateBar}]\``,
              image: { url: rateImg.url },
              color: rateColor,
              footer: { text: 'Powered by pure vibes' },
            });
          } else if (rateMentionMatch) {
            const rateUserId = rateMentionMatch[1];
            const rateUserRes = await rest('GET', `/users/${rateUserId}`, null, token).catch(() => null);
            const rateUser = rateUserRes?.status === 200 ? rateUserRes.data : null;
            const rateAvatarUrl = rateUser?.avatar
              ? `https://cdn.discordapp.com/avatars/${rateUserId}/${rateUser.avatar}.png?size=256`
              : `https://cdn.discordapp.com/embed/avatars/${(parseInt(rateUserId) >> 22) % 6}.png`;
            await replyEmbed(interaction, token, {
              title: `${rateScore}/10`,
              description: `<@${rateUserId}>\n\`[${rateBar}]\``,
              thumbnail: { url: rateAvatarUrl },
              color: rateColor,
              footer: { text: 'Powered by pure vibes' },
            });
          } else if (thing) {
            await replyEmbed(interaction, token, {
              title: `${rateScore}/10`,
              description: `**${thing}**\n\`[${rateBar}]\``,
              color: rateColor,
              footer: { text: 'Powered by pure vibes' },
            });
          } else {
            await reply(interaction, token, 'Give me something to rate! Text, an image, or @mention a user.', true);
          }
          break;
        }
        case 'ship': {
          const u1 = getOpt(interaction, 'user1'), u2 = getOpt(interaction, 'user2');
          if (!u1 || !u2) { await reply(interaction, token, 'Two users required.', true); break; }
          const key = [u1, u2].sort().join(':');
          let h = 0; for (let i = 0; i < key.length; i++) h = ((h << 5) - h + key.charCodeAt(i)) | 0;
          const pct = Math.abs(h) % 101;
          const filled = Math.round(pct / 10);
          const bar = '█'.repeat(filled) + '░'.repeat(10 - filled);
          await replyEmbed(interaction, token, { title: '\uD83D\uDC98 Compatibility', description: `<@${u1}>  +  <@${u2}>\n\`${bar}\` **${pct}%**`, color: 0xeb459e });
          break;
        }
        case 'fact': {
          try {
            const r = await httpFetch('GET', 'https://uselessfacts.jsph.pl/api/v2/facts/random?language=en');
            const d = typeof r.data === 'string' ? JSON.parse(r.data) : r.data;
            await reply(interaction, token, d?.text || 'No fact found.');
          } catch (e) { await reply(interaction, token, `Fact error: ${e.message}`, true); }
          break;
        }
        case 'quote': {
          const FALLBACK_QUOTES = [
            { q: "The only way to do great work is to love what you do.", a: "Steve Jobs" },
            { q: "In the middle of every difficulty lies opportunity.", a: "Albert Einstein" },
            { q: "It does not matter how slowly you go as long as you do not stop.", a: "Confucius" },
            { q: "Life is what happens when you're busy making other plans.", a: "John Lennon" },
            { q: "The future belongs to those who believe in the beauty of their dreams.", a: "Eleanor Roosevelt" },
            { q: "Believe you can and you're halfway there.", a: "Theodore Roosevelt" },
            { q: "In the end, it's not the years in your life that count. It's the life in your years.", a: "Abraham Lincoln" },
          ];
          try {
            const r = await httpFetch('GET', 'https://zenquotes.io/api/random');
            let parsed;
            try { parsed = typeof r.data === 'string' ? JSON.parse(r.data) : r.data; } catch {}
            const q = Array.isArray(parsed) ? parsed[0] : null;
            if (q?.q && q?.a) {
              await replyEmbed(interaction, token, { description: `> *"${q.q}"*`, author: { name: `— ${q.a}` }, color: 0xa78bfa, footer: { text: 'zenquotes.io' } });
            } else throw new Error('no data');
          } catch {
            const fb = FALLBACK_QUOTES[Math.floor(Math.random() * FALLBACK_QUOTES.length)];
            await replyEmbed(interaction, token, { description: `> *"${fb.q}"*`, author: { name: `— ${fb.a}` }, color: 0xa78bfa });
          }
          break;
        }
        case 'meme': {
          const sub = getOpt(interaction, 'subreddit') || 'memes';
          try {
            const r = await httpFetch('GET', `https://meme-api.com/gimme/${encodeURIComponent(sub)}`);
            const d = typeof r.data === 'string' ? JSON.parse(r.data) : r.data;
            if (!d?.url) throw new Error('no meme');
            await replyEmbed(interaction, token, { title: d.title || 'Meme', url: d.postLink, image: { url: d.url }, footer: { text: `r/${d.subreddit} • \u2191 ${d.ups || 0}` }, color: 0xff4500 });
          } catch (e) { await reply(interaction, token, `Meme error: ${e.message}`, true); }
          break;
        }
        case 'trivia': {
          const cat = getOpt(interaction, 'category');
          const catMap = { general: 9, science: 17, history: 23, gaming: 15, anime: 31, music: 12 };
          const cid = catMap[cat];
          try {
            const r = await httpFetch('GET', `https://opentdb.com/api.php?amount=1&type=multiple${cid ? `&category=${cid}` : ''}`);
            const d = typeof r.data === 'string' ? JSON.parse(r.data) : r.data;
            const q = d?.results?.[0];
            if (!q) throw new Error('no question');
            const decode = s => s.replace(/&quot;/g,'"').replace(/&#039;/g,"'").replace(/&amp;/g,'&').replace(/&rsquo;/g,"'").replace(/&ldquo;/g,'"').replace(/&rdquo;/g,'"').replace(/&lt;/g,'<').replace(/&gt;/g,'>');
            const all = [...q.incorrect_answers, q.correct_answer].sort(() => Math.random() - 0.5).map(decode);
            const correctIndex = all.indexOf(decode(q.correct_answer)) + 1;
            const NUM_EMOJIS = ['1️⃣','2️⃣','3️⃣','4️⃣'];
            const options = all.map((a, i) => `${NUM_EMOJIS[i]} ${a}`).join('\n');
            triviaSessions.set(channelId, {
              correctAnswer: decode(q.correct_answer),
              correctIndex,
              category: decode(q.category),
              questioner: caller.id,
              expiresAt: Date.now() + 90000,
            });
            setTimeout(() => { if (triviaSessions.get(channelId)?.questioner === caller.id) triviaSessions.delete(channelId); }, 90000);
            await replyEmbed(interaction, token, {
              title: `🧠 Trivia — ${decode(q.category)}`,
              description: `**${decode(q.question)}**\n\n${options}\n\n*Type **1**, **2**, **3**, or **4** to answer! You have 90 seconds.*`,
              color: 0xa78bfa,
              footer: { text: `Difficulty: ${q.difficulty}` },
            });
          } catch (e) { await reply(interaction, token, `Trivia error: ${e.message}`, true); }
          break;
        }
        case 'roast': {
          const u = getOpt(interaction, 'user');
          const roasts = [
            "you bring everyone so much joy — when you leave the room.",
            "you're not stupid, you just have bad luck thinking.",
            "I would agree with you, but then we'd both be wrong.",
            "you have the perfect face for radio.",
            "you're proof that even evolution takes a break sometimes.",
            "if I had a dollar for every brain cell you had, I'd have ten cents.",
            "you're like a cloud — when you disappear, it's a beautiful day."
          ];
          const r = roasts[Math.floor(Math.random() * roasts.length)];
          await reply(interaction, token, u ? `<@${u}>, ${r}` : r);
          break;
        }
        case 'compliment': {
          const u = getOpt(interaction, 'user');
          const lines = [
            "you have the best vibes in this server.",
            "your energy is genuinely contagious.",
            "you make everyone around you better.",
            "if kindness was a currency, you'd be loaded.",
            "the world is lucky to have you in it.",
            "you're the reason good things happen here."
          ];
          const r = lines[Math.floor(Math.random() * lines.length)];
          await reply(interaction, token, u ? `<@${u}>, ${r}` : r);
          break;
        }
        case 'would-you-rather': {
          const wyr = [
            'live without music, or live without movies?',
            'be able to fly, or be invisible at will?',
            'have unlimited pizza for life, or unlimited sushi for life?',
            'always have slow internet, or always have a slow computer?',
            'know the date of your death, or the cause?',
            'lose all your old memories, or never be able to make new ones?'
          ];
          await reply(interaction, token, `**Would you rather...** ${wyr[Math.floor(Math.random() * wyr.length)]}`);
          break;
        }
        case 'truth-or-dare': {
          const type = (getOpt(interaction, 'type') || 'random').toLowerCase();
          const truths = [
            "what's the most embarrassing thing on your phone right now?",
            "who in this server would you trust with your password?",
            "what's a lie you told that got way out of hand?",
            "what's the weirdest thing you've googled this month?",
            "who was your biggest crush in school?"
          ];
          const dares = [
            "change your Discord status to 'I'm losing at Trivia' for an hour.",
            "send the 5th photo in your camera roll (sfw).",
            "DM a random server member a compliment.",
            "type only in lowercase for the next 10 messages.",
            "post your most recent selfie."
          ];
          const pick = type === 'truth' ? truths : type === 'dare' ? dares : (Math.random() < 0.5 ? truths : dares);
          await reply(interaction, token, `**${pick === truths ? 'Truth' : 'Dare'}:** ${pick[Math.floor(Math.random() * pick.length)]}`);
          break;
        }
        case 'roleinfo': {
          const roleId = getOpt(interaction, 'role');
          const rr = await rest('GET', `/guilds/${guildId}/roles`, null, token);
          const role = (rr.data || []).find(r => r.id === roleId);
          if (!role) { await reply(interaction, token, 'Role not found.', true); break; }
          await replyEmbed(interaction, token, {
            title: role.name, color: role.color || 0x5865f2,
            fields: [
              { name: 'ID', value: role.id, inline: true },
              { name: 'Mentionable', value: role.mentionable ? 'Yes' : 'No', inline: true },
              { name: 'Hoisted', value: role.hoist ? 'Yes' : 'No', inline: true },
              { name: 'Position', value: String(role.position), inline: true },
              { name: 'Managed', value: role.managed ? 'Yes' : 'No', inline: true }
            ]
          });
          break;
        }
        case 'channelinfo': {
          const cid = getOpt(interaction, 'channel') || channelId;
          const cr = await rest('GET', `/channels/${cid}`, null, token);
          if (cr.status !== 200) { await reply(interaction, token, 'Channel not found.', true); break; }
          const c = cr.data;
          const types = { 0:'Text', 2:'Voice', 4:'Category', 5:'Announcement', 13:'Stage', 15:'Forum' };
          await replyEmbed(interaction, token, {
            title: `#${c.name}`, color: 0x5865f2,
            fields: [
              { name: 'ID', value: c.id, inline: true },
              { name: 'Type', value: types[c.type] || String(c.type), inline: true },
              { name: 'NSFW', value: c.nsfw ? 'Yes' : 'No', inline: true },
              { name: 'Slowmode', value: c.rate_limit_per_user ? `${c.rate_limit_per_user}s` : 'Off', inline: true },
              { name: 'Topic', value: c.topic || '-', inline: false }
            ]
          });
          break;
        }
        case 'permissions': {
          const targetId = getOpt(interaction, 'user') || caller.id;
          let perms;
          if (targetId === caller.id) {
            perms = BigInt(interaction.member?.permissions || '0');
          } else {
            const [memRes, rolesRes] = await Promise.all([
              rest('GET', `/guilds/${guildId}/members/${targetId}`, null, token),
              rest('GET', `/guilds/${guildId}/roles`, null, token)
            ]);
            if (memRes.status !== 200) { await reply(interaction, token, 'Could not fetch that user.', true); break; }
            const memRoleIds = new Set(memRes.data.roles || []);
            const allRoles = Array.isArray(rolesRes.data) ? rolesRes.data : [];
            perms = 0n;
            for (const role of allRoles) {
              if (role.id === guildId || memRoleIds.has(role.id)) perms |= BigInt(role.permissions);
            }
            if (perms & (1n << 3n)) perms = 0xFFFFFFFFn; // admin = all perms
          }
          const PERM_NAMES = {
            ADMINISTRATOR: 1n<<3n, MANAGE_GUILD: 1n<<5n, MANAGE_ROLES: 1n<<28n, MANAGE_CHANNELS: 1n<<4n,
            KICK_MEMBERS: 1n<<1n, BAN_MEMBERS: 1n<<2n, MANAGE_MESSAGES: 1n<<13n, MENTION_EVERYONE: 1n<<17n,
            SEND_MESSAGES: 1n<<11n, VIEW_CHANNEL: 1n<<10n, ATTACH_FILES: 1n<<15n, EMBED_LINKS: 1n<<14n,
            CONNECT: 1n<<20n, SPEAK: 1n<<21n, MOVE_MEMBERS: 1n<<24n, MUTE_MEMBERS: 1n<<22n,
            MANAGE_EMOJIS: 1n<<30n, DEAFEN_MEMBERS: 1n<<23n, CREATE_INVITE: 1n<<0n
          };
          const has = Object.entries(PERM_NAMES).filter(([,bit]) => (perms & bit) === bit).map(([n]) => n);
          await reply(interaction, token, `<@${targetId}> permissions: ${has.length ? has.map(p => `\`${p}\``).join(', ') : 'none notable'}`);
          break;
        }
        case 'emotes': {
          const gr = await rest('GET', `/guilds/${guildId}/emojis`, null, token);
          if (gr.status !== 200) { await reply(interaction, token, 'Could not fetch emojis.', true); break; }
          const list = (gr.data || []).map(e => `<${e.animated ? 'a' : ''}:${e.name}:${e.id}>`).join(' ').slice(0, 4000);
          await reply(interaction, token, list || 'No custom emojis.');
          break;
        }
        case 'firstmessage': {
          const ch = await rest('GET', `/channels/${channelId}`, null, token);
          const firstId = ch.data?.id;
          if (!firstId) { await reply(interaction, token, 'Could not fetch channel.', true); break; }
          const msgs = await rest('GET', `/channels/${channelId}/messages?after=0&limit=1`, null, token);
          const m = (msgs.data || [])[0];
          if (!m) { await reply(interaction, token, 'No messages found.', true); break; }
          await reply(interaction, token, `First message: https://discord.com/channels/${guildId}/${channelId}/${m.id}\n> ${m.content?.slice(0, 500) || '(no text)'}`);
          break;
        }
        case 'warnings': {
          const wTargetId = getOpt(interaction, 'user');
          if (!wTargetId) { await reply(interaction, token, 'Specify a user.', true); break; }
          const wKey = `${guildId}:${wTargetId}`;
          const userWarns = warnLog.get(wKey) || [];
          if (!userWarns.length) { await reply(interaction, token, `<@${wTargetId}> has no warnings on record.`); break; }
          await replyEmbed(interaction, token, {
            title: `⚠️ Warnings — ${userWarns.length} total`, color: 0xfee75c,
            description: userWarns.map((w, i) => `**${i+1}.** ${w}`).join('\n').slice(0, 4000)
          });
          break;
        }
        case 'nuke': {
          const nukeGuildRes = await rest('GET', `/guilds/${guildId}`, null, token);
          if (nukeGuildRes.status !== 200 || caller.id !== nukeGuildRes.data?.owner_id) {
            await reply(interaction, token, '🔒 Only the **server owner** can use the nuke command.', true);
            break;
          }
          const chRes = await rest('GET', `/channels/${channelId}`, null, token);
          if (chRes.status !== 200) { await reply(interaction, token, 'Could not fetch channel info.', true); break; }
          const ch = chRes.data;
          const newCh = await rest('POST', `/guilds/${guildId}/channels`, {
            name: ch.name, type: ch.type, topic: ch.topic, nsfw: ch.nsfw,
            position: ch.position, permission_overwrites: ch.permission_overwrites, parent_id: ch.parent_id
          }, token);
          if (newCh.status < 200 || newCh.status >= 300) { await reply(interaction, token, `Could not create replacement channel: ${newCh.data?.message || 'error'}`, true); break; }
          await rest('DELETE', `/channels/${channelId}`, null, token);
          rest('POST', `/channels/${newCh.data.id}/messages`, { content: `💥 Channel nuked by <@${caller.id}>.` }, token).catch(() => {});
          break;
        }
        case 'autorole': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const arId = getOpt(interaction, 'role');
          if (!arId) { await reply(interaction, token, 'Specify a role.', true); break; }
          guildAutoRole.set(guildId, arId);
          await reply(interaction, token, `✅ Auto-role set to <@&${arId}>. New members will receive this role on join.\n> Note: Requires **Server Members Intent** to be enabled in the Discord Developer Portal.`);
          break;
        }
        case 'welcome': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const wcChanId = getOpt(interaction, 'channel');
          const wcMsg = getOpt(interaction, 'message');
          if (!wcChanId || !wcMsg) { await reply(interaction, token, 'Channel and message are required.', true); break; }
          const wcTitle = getOpt(interaction, 'title') || 'Welcome!';
          const wcColorRaw = (getOpt(interaction, 'color') || '').replace('#', '');
          const wcColorParsed = wcColorRaw ? parseInt(wcColorRaw, 16) : NaN;
          const wcColor = isNaN(wcColorParsed) ? 0x5865f2 : wcColorParsed;
          const wcThumbnail = getOpt(interaction, 'thumbnail') !== false;
          const wcFooter = getOpt(interaction, 'footer') || '';
          const wcImage = getOpt(interaction, 'image') || '';
          guildWelcome.set(guildId, { channelId: wcChanId, message: wcMsg, title: wcTitle, color: wcColor, thumbnail: wcThumbnail, footer: wcFooter, image: wcImage });
          await replyEmbed(interaction, token, {
            title: '✅ Welcome Embed Configured',
            description: `New member messages will be sent to <#${wcChanId}>.`,
            color: wcColor,
            fields: [
              { name: 'Placeholders', value: '`{user}` — mention\n`{username}` — display name\n`{server}` — server name\n`{count}` — member count', inline: false },
              { name: 'Note', value: 'Requires **Server Members Intent** enabled in Discord Developer Portal → Bot → Privileged Gateway Intents.', inline: false },
            ],
            footer: { text: 'Preview reflects your color choice' },
          });
          break;
        }
        case 'goodbye': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const gcChanId = getOpt(interaction, 'channel');
          const gcMsg = getOpt(interaction, 'message');
          if (!gcChanId || !gcMsg) { await reply(interaction, token, 'Channel and message are required.', true); break; }
          const gcTitle = getOpt(interaction, 'title') || 'Goodbye';
          const gcColorRaw = (getOpt(interaction, 'color') || '').replace('#', '');
          const gcColorParsed = gcColorRaw ? parseInt(gcColorRaw, 16) : NaN;
          const gcColor = isNaN(gcColorParsed) ? 0xed4245 : gcColorParsed;
          const gcThumbnail = getOpt(interaction, 'thumbnail') !== false;
          guildGoodbye.set(guildId, { channelId: gcChanId, message: gcMsg, title: gcTitle, color: gcColor, thumbnail: gcThumbnail });
          await replyEmbed(interaction, token, {
            title: '✅ Goodbye Embed Configured',
            description: `Departure messages will be sent to <#${gcChanId}>.`,
            color: gcColor,
            fields: [
              { name: 'Placeholders', value: '`{user}` — mention\n`{username}` — display name\n`{server}` — server name', inline: false },
            ],
          });
          break;
        }
        case 'reactionrole': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const rrChanId = getOpt(interaction, 'channel');
          if (!rrChanId) { await reply(interaction, token, 'Channel required.', true); break; }
          const rrTitle = getOpt(interaction, 'title') || 'React for Roles';
          const rrIntro = getOpt(interaction, 'description') || '';
          const rrColorRaw = (getOpt(interaction, 'color') || '').replace('#', '');
          const rrColorParsed = rrColorRaw ? parseInt(rrColorRaw, 16) : NaN;
          const rrColor = isNaN(rrColorParsed) ? 0x5865f2 : rrColorParsed;
          // Collect up to 5 emoji+role pairs (emoji is optional — defaults to numbered emoji)
          const RR_DEFAULT_EMOJIS = ['1️⃣','2️⃣','3️⃣','4️⃣','5️⃣'];
          const rrPairs = [];
          for (let i = 1; i <= 5; i++) {
            const rawEmoji = getOpt(interaction, `emoji${i}`);
            const r = getOpt(interaction, `role${i}`);
            if (r) rrPairs.push({ emoji: normalizeDiscordEmoji(rawEmoji || RR_DEFAULT_EMOJIS[i - 1]), roleId: r });
          }
          if (!rrPairs.length) { await reply(interaction, token, 'Provide at least role1.', true); break; }
          // Filter out any roles that have elevated/mod permissions
          const _guildRolesRes = await rest('GET', `/guilds/${guildId}/roles`, null, token).catch(() => null);
          const _guildRoleMap = {};
          if (_guildRolesRes?.status === 200) for (const r of (_guildRolesRes.data || [])) _guildRoleMap[r.id] = r;
          const _filteredPairs = rrPairs.filter(p => { const r = _guildRoleMap[p.roleId]; return !r || !_isElevatedRole(r); });
          const _skipped = rrPairs.length - _filteredPairs.length;
          if (!_filteredPairs.length) { await reply(interaction, token, '❌ All provided roles have elevated/mod permissions and cannot be self-assigned by members.', true); break; }
          const rrLines = _filteredPairs.map(p => `${p.emoji}  →  <@&${p.roleId}>`).join('\n');
          const rrBody = (rrIntro ? rrIntro + '\n\n' : '') + rrLines;
          const rrMsgRes = await rest('POST', `/channels/${rrChanId}/messages`, {
            embeds: [{
              title: rrTitle,
              description: rrBody,
              color: rrColor,
              footer: { text: 'React to get a role • Remove your reaction to lose it' },
            }]
          }, token);
          if (rrMsgRes.status < 200 || rrMsgRes.status >= 300) { await reply(interaction, token, `Could not post message: ${rrMsgRes.data?.message || 'error'}`, true); break; }
          const rrMsgId = rrMsgRes.data.id;
          const rrRoleMap = {};
          for (const p of _filteredPairs) {
            rrRoleMap[p.emoji] = p.roleId;
            await rest('PUT', `/channels/${rrChanId}/messages/${rrMsgId}/reactions/${encodeURIComponent(p.emoji)}/@me`, null, token).catch(() => {});
          }
          reactionRoles.set(`${guildId}:${rrMsgId}`, { channelId: rrChanId, roles: rrRoleMap });
          const _skipNote = _skipped > 0 ? ` (${_skipped} elevated-permission role${_skipped !== 1 ? 's were' : ' was'} excluded)` : '';
          await reply(interaction, token, `✅ Reaction role menu posted in <#${rrChanId}>${_skipNote}. Use \`/reactionrole-add\` to add more pairs later (message ID: \`${rrMsgId}\`).`, true);
          break;
        }
        case 'reactionrole-add': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const rraMsgId = getOpt(interaction, 'message_id');
          const rraEmoji = getOpt(interaction, 'emoji');
          const rraRoleId = getOpt(interaction, 'role');
          const rraChanId = getOpt(interaction, 'channel') || channelId;
          if (!rraMsgId || !rraEmoji || !rraRoleId) { await reply(interaction, token, 'message_id, emoji, and role are all required.', true); break; }
          const rraKey = `${guildId}:${rraMsgId}`;
          if (!reactionRoles.has(rraKey)) reactionRoles.set(rraKey, { channelId: rraChanId, roles: {} });
          const rraEntry = reactionRoles.get(rraKey);
          const rraEmojiNorm = normalizeDiscordEmoji(rraEmoji);
          rraEntry.roles[rraEmojiNorm] = rraRoleId;
          const reactionChanId = rraEntry.channelId || rraChanId;
          // Add bot reaction so members see the clickable emoji
          await rest('PUT', `/channels/${reactionChanId}/messages/${rraMsgId}/reactions/${encodeURIComponent(rraEmoji)}/@me`, null, token).catch(() => {});
          // Update the embed to include the new pair
          const existingMsg = await rest('GET', `/channels/${reactionChanId}/messages/${rraMsgId}`, null, token).catch(() => null);
          if (existingMsg?.status === 200 && existingMsg.data?.embeds?.[0]) {
            const oldEmbed = existingMsg.data.embeds[0];
            const newLine = `${rraEmoji}  →  <@&${rraRoleId}>`;
            const oldDesc = oldEmbed.description || '';
            const newDesc = oldDesc ? oldDesc + '\n' + newLine : newLine;
            await rest('PATCH', `/channels/${reactionChanId}/messages/${rraMsgId}`, {
              embeds: [{ ...oldEmbed, description: newDesc }]
            }, token).catch(() => {});
          }
          await reply(interaction, token, `✅ Added ${rraEmoji} → <@&${rraRoleId}> to the reaction role menu.`, true);
          break;
        }
        case 'starboard': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const sbChanId = getOpt(interaction, 'channel');
          const sbThresh = Math.max(1, parseInt(getOpt(interaction, 'threshold') || '3', 10));
          if (!sbChanId) { await reply(interaction, token, 'Channel required.', true); break; }
          starboards.set(guildId, { channelId: sbChanId, threshold: sbThresh, posted: new Set() });
          await reply(interaction, token, `⭐ Starboard active! Messages with **${sbThresh}+ ⭐** reactions will be reposted to <#${sbChanId}>.`);
          break;
        }
        case 'autodelete': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const adChanId = getOpt(interaction, 'channel') || channelId;
          const adSecs = parseInt(getOpt(interaction, 'seconds') || '0', 10);
          if (adSecs === 0) {
            autoDelete.delete(adChanId);
            await reply(interaction, token, `✅ Auto-delete disabled in <#${adChanId}>.`);
          } else {
            if (adSecs < 1 || adSecs > 86400) { await reply(interaction, token, 'Seconds must be 1–86400.', true); break; }
            autoDelete.set(adChanId, adSecs);
            await reply(interaction, token, `🗑️ Messages in <#${adChanId}> will be auto-deleted after **${adSecs}s**.`);
          }
          break;
        }
        case 'schedule': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const schTimeStr = getOpt(interaction, 'time') || '';
          const schChanId = getOpt(interaction, 'channel') || channelId;
          const schMsg = getOpt(interaction, 'message') || '';
          if (!schMsg) { await reply(interaction, token, 'Message required.', true); break; }
          const target = new Date(schTimeStr);
          if (isNaN(target.getTime())) { await reply(interaction, token, 'Invalid time format. Use e.g. `2025-12-25 09:00`', true); break; }
          const delay = target.getTime() - Date.now();
          if (delay < 0) { await reply(interaction, token, 'That time is in the past.', true); break; }
          if (delay > 7 * 24 * 3600 * 1000) { await reply(interaction, token, 'Cannot schedule more than 7 days in advance.', true); break; }
          setTimeout(() => rest('POST', `/channels/${schChanId}/messages`, { content: schMsg }, token).catch(() => {}), delay);
          await reply(interaction, token, `⏰ Message scheduled for **${target.toUTCString()}** in <#${schChanId}>.`);
          break;
        }
        case 'announce': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const annChanId = getOpt(interaction, 'channel');
          const annTitle = getOpt(interaction, 'title') || 'Announcement';
          const annMsg = getOpt(interaction, 'message') || '';
          const annColor = parseInt((getOpt(interaction, 'color') || '#5865f2').replace('#',''), 16);
          const annImage = getOpt(interaction, 'image');
          const annThumb = getOpt(interaction, 'thumbnail');
          if (!annChanId || !annMsg) { await reply(interaction, token, 'Channel and message are required.', true); break; }
          const annEmbed = {
            title: annTitle,
            description: annMsg,
            color: isNaN(annColor) ? 0x5865f2 : annColor,
            timestamp: new Date().toISOString(),
            ...(annImage && /^https?:\/\//.test(annImage) ? { image: { url: annImage } } : {}),
            ...(annThumb && /^https?:\/\//.test(annThumb) ? { thumbnail: { url: annThumb } } : {})
          };
          const ar = await rest('POST', `/channels/${annChanId}/messages`, { embeds: [annEmbed] }, token);
          if (ar.status >= 200 && ar.status < 300) await reply(interaction, token, `📣 Announcement sent to <#${annChanId}>!`);
          else await reply(interaction, token, `Failed to send: ${ar.data?.message || 'Missing permissions'}`, true);
          break;
        }
        case 'nsfw-toggle': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          if (nsfwChannels.has(channelId)) {
            nsfwChannels.delete(channelId);
            _saveNsfwState(nsfwChannels, nsfwRoles);
            await reply(interaction, token, '🔒 NSFW commands **disabled** in this channel.', true);
          } else {
            nsfwChannels.add(channelId);
            _saveNsfwState(nsfwChannels, nsfwRoles);
            await reply(interaction, token, '🔞 NSFW commands **enabled** in this channel. You only need to do this once — the setting persists.', true);
          }
          break;
        }
        case 'nsfw-lock': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const nsfwRoleId = getOpt(interaction, 'role');
          if (!nsfwRoleId) { await reply(interaction, token, 'Role required.', true); break; }
          nsfwRoles.set(guildId, nsfwRoleId);
          _saveNsfwState(nsfwChannels, nsfwRoles);
          await reply(interaction, token, `🔞 NSFW commands are now restricted to members with <@&${nsfwRoleId}>.`, true);
          break;
        }

        // ── NSFW Auto-post — drops porn on a timer into a channel ──
        case 'nsfw-autopost': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const apAction = getOpt(interaction, 'action');

          if (apAction === 'stop') {
            const guildFeeds = _apGuildFeeds(guildId);

            // ── Stop by feed number (most precise — matches the N in "Feed N" from /list) ──
            const feedNumRaw = getOpt(interaction, 'feed');
            if (feedNumRaw !== null && feedNumRaw !== undefined) {
              const feedNum = parseInt(feedNumRaw, 10);
              const target = guildFeeds[feedNum - 1];
              if (target) {
                const [key, feed] = target;
                nsfwAutopost.delete(key);
                let catLabel;
                if (feed.category === '__random__') catLabel = 'random (all categories)';
                else if (Array.isArray(feed.categories)) catLabel = feed.categories.join(', ');
                else catLabel = feed.category || '?';
                await reply(interaction, token, `⏹️ **Feed ${feedNum}** stopped — was posting **${catLabel}** in <#${feed.targetChannelId}>.`, true);
              } else {
                await reply(interaction, token, `❌ No Feed ${feedNum} exists. There are currently **${guildFeeds.length}** feed${guildFeeds.length !== 1 ? 's' : ''} running. Use \`/nsfw-autopost action:list\` to see them.`, true);
              }
              break;
            }

            // ── Stop by category (stops the first matching feed in the target channel) ──
            const stopTargetChannelId = getOpt(interaction, 'channel') || channelId;
            const stopCat = [
              getOpt(interaction, 'category'),
              getOpt(interaction, 'category2'),
              getOpt(interaction, 'category3'),
              getOpt(interaction, 'category4'),
            ].filter(Boolean).map(v => v.toLowerCase().trim()).find(v => v in AP_CAT_QUERIES) || '';
            if (stopCat) {
              const matchEntry = guildFeeds.find(([, f]) =>
                f.targetChannelId === stopTargetChannelId &&
                (f.category === stopCat || (Array.isArray(f.categories) && f.categories.includes(stopCat)))
              );
              if (matchEntry) { nsfwAutopost.delete(matchEntry[0]); }
              await reply(interaction, token, matchEntry
                ? `⏹️ Auto posting for **${stopCat}** stopped in <#${stopTargetChannelId}>.`
                : `⏹️ No feed for **${stopCat}** found in <#${stopTargetChannelId}>. Use \`/nsfw-autopost action:list\` to see active feeds.`, true);
              break;
            }

            // ── Stop all feeds in a specific channel ──
            const keysToStop = guildFeeds
              .filter(([, f]) => f.targetChannelId === stopTargetChannelId)
              .map(([k]) => k);
            keysToStop.forEach(k => { nsfwAutopost.delete(k); });
            await reply(interaction, token, keysToStop.length > 0
              ? `⏹️ All auto posting stopped in <#${stopTargetChannelId}> (${keysToStop.length} feed${keysToStop.length !== 1 ? 's' : ''}).`
              : `⏹️ No auto posting was running in <#${stopTargetChannelId}>.`, true);
            break;
          }

          if (apAction === 'list') {
            const guildFeeds = _apGuildFeeds(guildId);
            if (!guildFeeds.length) {
              await replyEmbed(interaction, token, {
                title: '🔞 Autopost Feeds',
                description: 'No autopost feeds are currently running in this server.',
                color: 0x2b2d31,
              });
              break;
            }
            const fields = guildFeeds.map(([key, feed], idx) => {
              const feedChannelId = feed.targetChannelId || channelId;
              const intervalLabel = `Every ${feed.intervalMin} min`;
              let catLabel;
              if (feed.category === '__random__') {
                catLabel = '🎲 Random (all categories)';
              } else if (Array.isArray(feed.categories)) {
                catLabel = feed.categories.map(c => (AP_CAT_EMOJI[c] || '🔞') + ' ' + c).join(', ');
              } else {
                catLabel = (AP_CAT_EMOJI[feed.category] || '🔞') + ' ' + (feed.category || '?');
              }
              return {
                name: `Feed ${idx + 1} — <#${feedChannelId}>`,
                value: `**Categories:** ${catLabel}\n**Interval:** ${intervalLabel}`,
                inline: false,
              };
            });
            await replyEmbed(interaction, token, {
              title: `🔞 Active Autopost Feeds — ${guildFeeds.length}/5 running`,
              color: 0xe879f9,
              fields,
              footer: { text: 'Stop a specific feed: /nsfw-autopost action:stop feed:N  •  Stop by channel: /nsfw-autopost action:stop channel:#ch' },
            });
            break;
          }

          // start
          if (!nsfwChannels.has(channelId)) {
            await reply(interaction, token, '🔞 NSFW must be enabled in this channel first. Run `/nsfw-toggle`.', true); break;
          }

          // Collect all 4 category fields + any comma-separated values inside them
          const ALL_AP_CATS = Object.keys(AP_CAT_QUERIES);
          const _rawCats = [
            getOpt(interaction, 'category'),
            getOpt(interaction, 'category2'),
            getOpt(interaction, 'category3'),
            getOpt(interaction, 'category4'),
          ]
            .filter(Boolean)
            .flatMap(v => v.toLowerCase().split(/[\s,]+/))
            .map(s => s.trim())
            .filter(Boolean);

          const isRandom = _rawCats.some(s => s === 'random');
          const apCategories = isRandom
            ? ALL_AP_CATS
            : [...new Set(_rawCats.filter(s => s in AP_CAT_QUERIES))];

          if (!isRandom && apCategories.length === 0) {
            await reply(interaction, token,
              `❌ No valid categories found. Pick from the dropdown or type a category name.`, true); break;
          }

          const apIntervalMin      = parseInt(getOpt(interaction, 'interval') || '5');
          const apTargetChannelId  = getOpt(interaction, 'channel') || channelId;
          const apIntervalMs       = apIntervalMin * 60 * 1000;
          const botAvatarUrl       = botUser?.id && botUser?.avatar
            ? `https://cdn.discordapp.com/avatars/${botUser.id}/${botUser.avatar}.png`
            : null;

          if (isRandom) {
            // Single rotating feed — cycles through all categories in random order
            const apSlot = _apNextSlot(guildId);
            if (!apSlot) { await reply(interaction, token, '❌ Maximum of 5 autopost feeds are already running. Use `/nsfw-autopost action:stop` to stop one first.', true); break; }
            const apKey = `${guildId}:__ap__${apSlot}`;
            let _rotIdx = 0;
            const _rotOrder = [...ALL_AP_CATS].sort(() => Math.random() - 0.5);
            const randomAutoPostFn = async () => {
              const cat = _rotOrder[_rotIdx];
              _rotIdx++;
              if (_rotIdx >= _rotOrder.length) {
                // reshuffle after one full cycle — ensure the new first item differs
                // from what was just posted so no category appears back-to-back across cycles
                const lastPosted = _rotOrder[_rotOrder.length - 1];
                _rotOrder.sort(() => Math.random() - 0.5);
                if (_rotOrder[0] === lastPosted && _rotOrder.length > 1) {
                  const swapIdx = 1 + Math.floor(Math.random() * (_rotOrder.length - 1));
                  [_rotOrder[0], _rotOrder[swapIdx]] = [_rotOrder[swapIdx], _rotOrder[0]];
                }
                _rotIdx = 0;
              }
              const catQuery = AP_CAT_QUERIES[cat] || cat;
              const catEmoji = AP_CAT_EMOJI[cat] || '🔞';
              const catColor = AP_CAT_COLORS[cat] || 0xff0066;
              const catLabel = cat.charAt(0).toUpperCase() + cat.slice(1);
              try {
                // Use guild's persistent seenSet (capped at 500) so autopost never repeats a video.
                // Gifreels fallback guarantees content even when the cap fills up.
                const _apRawSeen = nsfwPostedIds.get(guildId) || new Set();
                const _apSeenSet = _apRawSeen.size > 500
                  ? new Set([..._apRawSeen].slice(-500))
                  : new Set(_apRawSeen);
                const _apSubs = AP_CAT_SUBS[cat] || NSFW_FALLBACK_SUBS;
                const _apRrKey = `ap:${guildId}:${cat}`;
                const _apRrIdx = _nsfwSubIndex.get(_apRrKey) || 0;
                const _apActiveSubs = [];
                for (let _i = 0; _i < 10; _i++) _apActiveSubs.push(_apSubs[(_apRrIdx + _i) % _apSubs.length]);
                _nsfwSubIndex.set(_apRrKey, (_apRrIdx + 10) % _apSubs.length);
                _saveNsfwSubIdx(_nsfwSubIndex);
                // Source rotation — 6 sources. Gifreels is NOT in this pool — it is the guaranteed
                // last-resort fallback so it never blocks redgifs or other sources from being selected.
                const _apSrcNames = ['reddvideo', 'reddxxx', 'redditporn', 'reddtastic', 'scrolller', 'redgifs'];
                const _apSrcKey = `ap:src:${guildId}:${cat}`;
                const _apSrcIdx = _nsfwSubIndex.get(_apSrcKey) || 0;
                _nsfwSubIndex.set(_apSrcKey, (_apSrcIdx + 1) % _apSrcNames.length);
                _saveNsfwSubIdx(_nsfwSubIndex);
                const _apTo = (p, ms) => Promise.race([p, new Promise(r => setTimeout(() => r(null), ms))]);
                const [rvp, rgp, rxp, rpp, rtp, slp] = await Promise.all([
                  _apTo(fetchReddvideoContent(cat, _apSeenSet), 10000),
                  _apTo(fetchRedgifsContent(catQuery, _apSeenSet, null), 10000),
                  _apTo(fetchReddxxxContent(cat, _apSeenSet), 8000),
                  _apTo(fetchRedditPorn(_apActiveSubs, _apSeenSet), 8000),
                  _apTo(fetchReddtasticContent(cat, _apSeenSet), 8000),
                  _apTo(fetchScrolllerContent(cat, _apSeenSet), 8000),
                ]);
                const _apSrcMap = { reddvideo: rvp, redditporn: rpp, redgifs: rgp, reddxxx: rxp, reddtastic: rtp, scrolller: slp };
                let post = null;
                for (let _i = 0; _i < _apSrcNames.length; _i++) {
                  const src = _apSrcNames[(_apSrcIdx + _i) % _apSrcNames.length];
                  if (_apSrcMap[src]) { post = _apSrcMap[src]; break; }
                }
                if (!post) post = await fetchReddvideoContent(cat, null).catch(() => null);
                if (!post) post = await fetchRedditPorn(_apActiveSubs, null).catch(() => null);
                if (!post) post = await fetchRedgifsContent(catQuery, null, null).catch(() => null);
                if (!post) post = await fetchGifreelsContent(cat, null).catch(() => null);
                const postUrl = post ? (post.videoUrl || post.url || null) : null;
                if (post && postUrl) {
                  if (!nsfwPostedIds.has(guildId)) nsfwPostedIds.set(guildId, new Set());
                  const _apPersist = nsfwPostedIds.get(guildId);
                  if (post.url)      _apPersist.add(post.url);
                  if (post.videoUrl) _apPersist.add(post.videoUrl);
                  if (post.id)       _apPersist.add(post.id);
                  _saveNsfwDedup(nsfwPostedIds);
                  const _apTitle = post.title ? `**${post.title.slice(0, 120)}**\n` : '';
                  const _apAuthor = post.author ? ` • u/${post.author}` : '';
                  const _apSrc = post.sub === 'redgifs' ? `🔞 Redgifs${_apAuthor}` : post.sub === 'gifreels' ? `🔞 Gifreels${_apAuthor}` : `🔞 r/${post.sub || cat}${_apAuthor}`;
                  await rest('POST', `/channels/${apTargetChannelId}/messages`, { content: `${_apTitle}${_apSrc}\n${postUrl}` }, _token);
                }
              } catch {}
            };
            nsfwAutopost.set(apKey, { postFn: randomAutoPostFn, category: '__random__', intervalMin: apIntervalMin, targetChannelId: apTargetChannelId });
            _apEnsureTicker();
            randomAutoPostFn();
            await reply(interaction, token,
              `✅ **Random rotating feed started** (Feed ${apSlot}/5) — cycles through all ${ALL_AP_CATS.length} categories in random order\n⏰ Posting every **${apIntervalMin} min** in <#${apTargetChannelId}>\nStop: \`/nsfw-autopost action:stop\``
            );
            break;
          }

          // One timer cycles through all selected categories in order — one post per tick.
          // This ensures every category gets equal airtime regardless of how many are selected.
          // Start at a random offset so restarts don't always give the first category an extra post.
          let _catIdx = Math.floor(Math.random() * apCategories.length);
          const multiAutoPostFn = async () => {
            const cat = apCategories[_catIdx % apCategories.length];
            _catIdx++;
            const catQuery = AP_CAT_QUERIES[cat] || cat;
            const catEmoji = AP_CAT_EMOJI[cat]  || '🔞';
            const catColor = AP_CAT_COLORS[cat] || 0xff0066;
            const catLabel = cat.charAt(0).toUpperCase() + cat.slice(1);
            try {
              // Use guild's persistent seenSet (capped at 500) so autopost never repeats a video.
              const _apRawSeen = nsfwPostedIds.get(guildId) || new Set();
              const _apSeenSet = _apRawSeen.size > 500
                ? new Set([..._apRawSeen].slice(-500))
                : new Set(_apRawSeen);
              const _apSubs = AP_CAT_SUBS[cat] || NSFW_FALLBACK_SUBS;
              const _apRrKey = `ap:${guildId}:${cat}`;
              const _apRrIdx = _nsfwSubIndex.get(_apRrKey) || 0;
              const _apActiveSubs = [];
              for (let _i = 0; _i < 10; _i++) _apActiveSubs.push(_apSubs[(_apRrIdx + _i) % _apSubs.length]);
              _nsfwSubIndex.set(_apRrKey, (_apRrIdx + 10) % _apSubs.length);
              _saveNsfwSubIdx(_nsfwSubIndex);
              // Source rotation — 6 sources. Gifreels is NOT in this pool — it is the guaranteed
              // last-resort fallback so it never blocks redgifs or other sources from being selected.
              const _apSrcNames = ['reddvideo', 'reddxxx', 'redditporn', 'reddtastic', 'scrolller', 'redgifs'];
              const _apSrcKey = `ap:src:${guildId}:${cat}`;
              const _apSrcIdx = _nsfwSubIndex.get(_apSrcKey) || 0;
              _nsfwSubIndex.set(_apSrcKey, (_apSrcIdx + 1) % _apSrcNames.length);
              _saveNsfwSubIdx(_nsfwSubIndex);
              const _mTo = (p, ms) => Promise.race([p, new Promise(r => setTimeout(() => r(null), ms))]);
              const [rvp, rgp, rxp, rpp, rtp, slp] = await Promise.all([
                _mTo(fetchReddvideoContent(cat, _apSeenSet), 10000),
                _mTo(fetchRedgifsContent(catQuery, _apSeenSet, null), 10000),
                _mTo(fetchReddxxxContent(cat, _apSeenSet), 8000),
                _mTo(fetchRedditPorn(_apActiveSubs, _apSeenSet), 8000),
                _mTo(fetchReddtasticContent(cat, _apSeenSet), 8000),
                _mTo(fetchScrolllerContent(cat, _apSeenSet), 8000),
              ]);
              const _apSrcMap = { reddvideo: rvp, redditporn: rpp, redgifs: rgp, reddxxx: rxp, reddtastic: rtp, scrolller: slp };
              let post = null;
              for (let _i = 0; _i < _apSrcNames.length; _i++) {
                const src = _apSrcNames[(_apSrcIdx + _i) % _apSrcNames.length];
                if (_apSrcMap[src]) { post = _apSrcMap[src]; break; }
              }
              if (!post) post = await fetchReddvideoContent(cat, null).catch(() => null);
              if (!post) post = await fetchRedditPorn(_apActiveSubs, null).catch(() => null);
              if (!post) post = await fetchRedgifsContent(catQuery, null, null).catch(() => null);
              if (!post) post = await fetchGifreelsContent(cat, null).catch(() => null);
              const postUrl = post ? (post.videoUrl || post.url || null) : null;
              if (post && postUrl) {
                if (!nsfwPostedIds.has(guildId)) nsfwPostedIds.set(guildId, new Set());
                const _apPersist = nsfwPostedIds.get(guildId);
                if (post.url)      _apPersist.add(post.url);
                if (post.videoUrl) _apPersist.add(post.videoUrl);
                if (post.id)       _apPersist.add(post.id);
                _saveNsfwDedup(nsfwPostedIds);
                const _apTitle = post.title ? `**${post.title.slice(0, 120)}**\n` : '';
                const _apAuthor = post.author ? ` • u/${post.author}` : '';
                const _apSrc = post.sub === 'redgifs' ? `🔞 Redgifs${_apAuthor}` : post.sub === 'gifreels' ? `🔞 Gifreels${_apAuthor}` : `🔞 r/${post.sub || cat}${_apAuthor}`;
                await rest('POST', `/channels/${apTargetChannelId}/messages`, { content: `${_apTitle}${_apSrc}\n${postUrl}` }, _token);
              }
            } catch {}
          };

          const apSlot = _apNextSlot(guildId);
          if (!apSlot) { await reply(interaction, token, '❌ Maximum of 5 autopost feeds are already running. Use `/nsfw-autopost action:stop` to stop one first.', true); break; }
          const apKey = `${guildId}:__ap__${apSlot}`;
          nsfwAutopost.set(apKey, { postFn: multiAutoPostFn, categories: apCategories, intervalMin: apIntervalMin, targetChannelId: apTargetChannelId });
          _apEnsureTicker();
          multiAutoPostFn();

          const startedLabels = apCategories.map(c => `${AP_CAT_EMOJI[c] || '🔞'} ${c.charAt(0).toUpperCase() + c.slice(1)}`);
          await reply(interaction, token,
            `✅ **Feed ${apSlot}/5 started** — ${startedLabels.length} categor${startedLabels.length !== 1 ? 'ies' : 'y'} cycling: ${startedLabels.join('  ·  ')}\n⏰ One post every **${apIntervalMin} min** in <#${apTargetChannelId}>, rotating through each in order\nStop: \`/nsfw-autopost action:stop\``
          );
          break;
        }

        // ── NSFW Dedupe — scan channel for duplicate bot messages and delete them ──
        case 'nsfw-dedupe': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          // Clear in-memory dedup history
          nsfwPostedIds.delete(guildId);
          await deferReply(true);

          try {
            // Fetch up to 500 messages in batches of 100
            const allMessages = [];
            let before = undefined;
            for (let i = 0; i < 5; i++) {
              const qs = before ? `?limit=100&before=${before}` : '?limit=100';
              const r = await rest('GET', `/channels/${channelId}/messages${qs}`, null, token);
              if (r.status !== 200 || !Array.isArray(r.data) || r.data.length === 0) break;
              allMessages.push(...r.data);
              before = r.data[r.data.length - 1].id;
              if (r.data.length < 100) break;
            }

            // Extract the "media key" from a message — embed image/video URL or attachment URL
            const getMediaKey = (msg) => {
              if (msg.author?.id !== botUser?.id) return null;
              // Plain content URL (redgifs watch links)
              if (msg.content && /https?:\/\/\S+/.test(msg.content)) {
                const m = msg.content.match(/https?:\/\/\S+/);
                if (m) return m[0].split('?')[0].toLowerCase();
              }
              // Embed image
              const emb = msg.embeds?.[0];
              if (emb?.image?.url) return emb.image.url.split('?')[0].toLowerCase();
              if (emb?.video?.url) return emb.video.url.split('?')[0].toLowerCase();
              // Attachment
              if (msg.attachments?.length) return msg.attachments[0].url.split('?')[0].split('_')[0].toLowerCase();
              return null;
            };

            const seen = new Map(); // mediaKey -> first message id
            const toDelete = [];
            // Messages come newest-first; reverse so we keep the oldest occurrence
            for (const msg of [...allMessages].reverse()) {
              const key = getMediaKey(msg);
              if (!key) continue;
              if (seen.has(key)) {
                toDelete.push(msg.id);
              } else {
                seen.set(key, msg.id);
              }
            }

            if (toDelete.length === 0) {
              await editReply('✅ **No duplicate posts found** in the last 500 messages. History cleared!');
              break;
            }

            // Bulk-delete (messages < 14 days old); fall back to individual deletes
            const twoWeeksAgo = Date.now() - 14 * 24 * 60 * 60 * 1000;
            const bulkIds = toDelete.filter(id => {
              const ts = Number(BigInt(id) >> 22n) + 1420070400000;
              return ts > twoWeeksAgo;
            });
            const oldIds = toDelete.filter(id => !bulkIds.includes(id));

            let deleted = 0;
            if (bulkIds.length >= 2) {
              // Bulk-delete in batches of 100
              for (let i = 0; i < bulkIds.length; i += 100) {
                const batch = bulkIds.slice(i, i + 100);
                const r = await rest('POST', `/channels/${channelId}/messages/bulk-delete`, { messages: batch }, token);
                if (r.status === 204) deleted += batch.length;
              }
            } else {
              oldIds.push(...bulkIds);
            }
            for (const id of oldIds) {
              const r = await rest('DELETE', `/channels/${channelId}/messages/${id}`, null, token);
              if (r.status === 204) deleted++;
              await new Promise(res => setTimeout(res, 600)); // rate-limit safe
            }

            await editReply(`🗑️ **Dedupe complete!** Deleted **${deleted}** duplicate post${deleted !== 1 ? 's' : ''} from the last 500 messages. History cleared!`);
          } catch (e) {
            await editReply(`❌ Dedupe scan failed: ${e.message || e}`);
          }
          break;
        }

        case 'setmodrole': {
          const callerPermsSmr = BigInt(interaction.member?.permissions || '0');
          if ((callerPermsSmr & 8n) !== 8n) { await reply(interaction, token, '❌ Only administrators can assign trusted mod roles.', true); break; }
          const smrRoleId = getOpt(interaction, 'role');
          if (!smrRoleId) { await reply(interaction, token, 'Role required.', true); break; }
          if (!guildModRoles.has(guildId)) guildModRoles.set(guildId, new Set());
          guildModRoles.get(guildId).add(smrRoleId);
          await reply(interaction, token, `✅ <@&${smrRoleId}> is now a trusted mod role and can use protected commands.`);
          break;
        }
        case 'removemodrole': {
          const callerPermsRmr = BigInt(interaction.member?.permissions || '0');
          if ((callerPermsRmr & 8n) !== 8n) { await reply(interaction, token, '❌ Only administrators can remove trusted mod roles.', true); break; }
          const rmrRoleId = getOpt(interaction, 'role');
          if (!rmrRoleId) { await reply(interaction, token, 'Role required.', true); break; }
          const rmrSet = guildModRoles.get(guildId);
          if (rmrSet?.has(rmrRoleId)) {
            rmrSet.delete(rmrRoleId);
            await reply(interaction, token, `✅ <@&${rmrRoleId}> removed from trusted mod roles.`);
          } else {
            await reply(interaction, token, `<@&${rmrRoleId}> is not a trusted mod role.`, true);
          }
          break;
        }
        case 'listmodroles': {
          const lmrSet = guildModRoles.get(guildId);
          if (!lmrSet?.size) { await reply(interaction, token, 'No trusted mod roles set. Use `/setmodrole` to add one.', true); break; }
          const list = [...lmrSet].map(id => `<@&${id}>`).join('\n');
          await replyEmbed(interaction, token, { title: '🛡️ Trusted Mod Roles', description: list, color: 0x5865f2 });
          break;
        }
        case 'nsfw-age-gate': {
          const ageChanId = getOpt(interaction, 'channel');
          const ageRoleId = getOpt(interaction, 'role');
          // Enforce nsfw-lock: only users with the locked role (or admin) can set up age gates
          const lockedRole = nsfwRoles.get(guildId);
          if (lockedRole) {
            const callerPerms = BigInt(interaction.member?.permissions || '0');
            const isAdmin = (callerPerms & (1n << 3n)) === (1n << 3n);
            const callerRoles = interaction.member?.roles || [];
            if (!isAdmin && !callerRoles.includes(lockedRole)) {
              await reply(interaction, token, `❌ NSFW commands are restricted to <@&${lockedRole}>. Run \`/nsfw-lock\` to change this.`, true);
              break;
            }
          }
          if (!ageChanId || !ageRoleId) { await reply(interaction, token, 'Channel and role are required.', true); break; }
          const ageRes = await rest('POST', `/channels/${ageChanId}/messages`, {
            embeds: [{
              title: '🔞 Age Verification Required',
              description: 'You must be **18 or older** to access NSFW content in this server.\n\nBy clicking the button below, you confirm that you are 18+ and consent to viewing adult content.',
              color: 0xed4245, footer: { text: 'Bot must be online for this button to work' }
            }],
            components: [{ type: 1, components: [{ type: 2, style: 4, label: '✅ I am 18+ — Verify Me', custom_id: `nsfw_age_gate:${ageRoleId}` }] }]
          }, token);
          if (ageRes.status >= 200 && ageRes.status < 300) await reply(interaction, token, `✅ Age gate posted in <#${ageChanId}>. Members who click will receive <@&${ageRoleId}>.`);
          else await reply(interaction, token, `Failed: ${ageRes.data?.message || 'error'}`, true);
          break;
        }
        case 'nsfw-stats': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const guildStats = [...nsfwCommandStats.entries()]
            .filter(([k]) => k.startsWith(`${guildId}:`))
            .map(([k, v]) => ({ cmd: k.split(':')[1], count: v }))
            .sort((a, b) => b.count - a.count);
          if (!guildStats.length) {
            await reply(interaction, token, '📊 No NSFW command usage recorded yet.', true); break;
          }
          const total = guildStats.reduce((s, x) => s + x.count, 0);
          const top = guildStats.slice(0, 15);
          const rows = top.map((x, i) => {
            const bar = '█'.repeat(Math.round((x.count / top[0].count) * 10));
            return `${i + 1}. **/${x.cmd}** — ${x.count} uses \`${bar}\``;
          }).join('\n');
          const activeFeeds = [...nsfwAutopost.keys()].filter(k => k.startsWith(`${guildId}:`)).length;
          const dedupCount = nsfwPostedIds.get(guildId)?.size || 0;
          await replyEmbed(interaction, token, {
            title: '📊 NSFW Command Stats',
            description: rows,
            color: 0x9b59b6,
            fields: [
              { name: 'Total Uses', value: `${total}`, inline: true },
              { name: 'Active Autopost Feeds', value: `${activeFeeds}`, inline: true },
              { name: 'Deduped Posts (this session)', value: `${dedupCount}`, inline: true },
            ],
            footer: { text: 'Stats reset on bot restart' },
          });
          break;
        }
        case 'nsfw-search': {
          if (!nsfwChannels.has(channelId)) {
            await reply(interaction, token, '🔞 NSFW commands can only be used in NSFW-enabled channels.', true); break;
          }
          await deferReply();
          const searchQuery = (getOpt(interaction, 'query') || '').trim();
          if (!searchQuery) { await editReply('❌ Please provide a search query.'); break; }
          const rgResult = await fetchRedgifsContent(searchQuery, undefined);
          if (rgResult) {
            await editReply({ content: rgResult.videoUrl });
          } else {
            await editReply('❌ No results found for that search. Try different keywords.');
          }
          break;
        }

        // ── NSFW content commands ──
        case 'ass': case 'pussy': case 'goth': case 'thick':
        case 'boobs': case 'hentai': case 'blowjob':
        case 'lesbian': case 'cum': case 'feet': case 'thighs':
        case 'nudes': case 'milf': case 'ebony': case 'asian':
        case 'redhead': case 'ahegao': case 'anal': case 'bondage':
        case 'latina': case 'petite': case 'blonde': case 'brunette':
        case 'bbw': case 'trans': case 'pov': case 'creampie':
        case 'squirt': case 'titfuck': case 'dp': case 'gangbang':
        case 'lingerie': case 'cosplay': case 'joi': case 'femdom':
        case 'leggings': case 'riding': case 'doggystyle': case 'handjob':
        case 'outdoor': case 'massage': case 'latex': case 'facesitting':
        case 'rimjob': case 'nsfw-gif': case 'nsfw-video': {
          if (!nsfwChannels.has(channelId)) {
            await reply(interaction, token, '🔞 NSFW commands can only be used in channels with NSFW enabled. A mod must run `/nsfw-toggle` first.', true);
            break;
          }
          // 5-second per-user cooldown
          const _cdNow = Date.now();
          const _cdLast = nsfwCooldowns.get(caller.id) || 0;
          if (_cdNow - _cdLast < 5000) {
            await reply(interaction, token, `⏳ Slow down! Wait ${((5000 - (_cdNow - _cdLast)) / 1000).toFixed(1)}s before using another NSFW command.`, true);
            break;
          }
          nsfwCooldowns.set(caller.id, _cdNow);
          // Track usage stats
          const _statKey = `${guildId}:${cmd}`;
          nsfwCommandStats.set(_statKey, (nsfwCommandStats.get(_statKey) || 0) + 1);
          // Defer immediately — Reddit HTTP calls can exceed the 3s interaction timeout
          await deferReply();
          const NSFW_SUBS = NSFW_CAT_SUBS;

          // Tag pools used for filtering search/niche results — must match Redgifs' own tag terminology.
          // Wide synonym lists so the filter finds matches even when Redgifs uses alternate spellings.
          const NSFW_QUERIES = {
            ass:         ['ass','bigass','pawg','booty','bigbooty','bigbutt','butt','roundass','thickass','assclapping','bubblebutt','buttjiggle'],
            pussy:       ['pussy','wetpussy','pussylicking','pussyeating','creampie','fingering','squirt','pussyclose','vagina','clit'],
            goth:        ['goth','altgirl','egirl','emo','gothic','punk','tattooedgirl','alternative'],
            thick:       ['thick','pawg','thicc','curvy','thickass','bigbooty','bigbutt','chubby','bbw'],
            boobs:       ['boobs','bigtits','tits','naturaltits','bigboobs','busty','hugetits','titties','naturalbusty','bignaturals'],
            hentai:      ['hentai','animehentai','anime','hentaisex','uncensored','animesex','ecchi','waifu'],
            blowjob:     ['blowjob','deepthroat','oral','throatfuck','sloppyblowjob','bj','sucking','cocksucker','throatpie'],
            lesbian:     ['lesbian','lesbians','girlongirl','girlongirlsex','lesbianpussy','scissoring','strap','straponsex'],
            cum:         ['cumshot','facial','cum','cumswallow','cuminmouth','cumdripping','swallow','moneyshot'],
            feet:        ['feet','footjob','soles','feetlicking','footfetish','toes','toesucking','footplay'],
            thighs:      ['thighs','thickhighs','thighhighs','thighsex','thighfuck','thighjob','thighsqueeze'],
            nudes:       ['nude','nakedgirl','selfie','amateurnude','nakedwomen','naked','solo','striptease'],
            milf:        ['milf','maturewomen','mature','milfpov','milfass','olderwoman','cougar'],
            ebony:       ['ebony','blackgirl','blackwoman','ebonyass','ebonysex','chocolate'],
            asian:       ['asian','japanese','korean','thai','chinese','asiangirl','asianporn'],
            redhead:     ['redhead','ginger','redheadsex','gingersnap','redheadblowjob'],
            ahegao:      ['ahegao','aheface','orgasmface','ahegaoface','odango'],
            anal:        ['anal','analsex','analplay','analcreampie','analgaping','assplay','backdoor','butt','butthole'],
            bondage:     ['bondage','bdsm','ropebondage','shibari','tied','restraint','hogtied','bound'],
            latina:      ['latina','latinasex','latinaass','latinabutt','latinariding','hispanic'],
            petite:      ['petite','petitegirl','tinyteen','small','skinny','smalltits','tinybody'],
            blonde:      ['blonde','blondesex','blondeblowjob','blonderiding','blondeass','bleached'],
            brunette:    ['brunette','brunettesex','darkhair','brunetteblowjob','blackhair'],
            bbw:         ['bbw','chubby','bbwass','bbwriding','bbwsex','plussize','fat','plump','curvy'],
            trans:       ['trans','tgirl','shemale','transsex','transriding','transgender','ladyboy'],
            pov:         ['pov','povblowjob','povriding','povdoggystyle','povfuck','pointofview','firstperson'],
            creampie:    ['creampie','creampiepussy','analcreampie','creampiedripping','internalcreampie','internal'],
            squirt:      ['squirt','squirting','gushing','squirtingorgasm','wetorgasm','squirtpussy','gush'],
            titfuck:     ['titfuck','paizuri','titjob','boobsjob','titfucking','tittyfuck','boobsex'],
            dp:          ['doublepenetration','dp','airtight','dpanal','doublepenetrated','twococks'],
            gangbang:    ['gangbang','threesome','groupsex','orgy','mmf','train','gangbangcreampie'],
            lingerie:    ['lingerie','stockings','thong','lace','suspenders','corset','garter','nylons'],
            cosplay:     ['cosplay','animecosplay','nsfwcosplay','cosplaysex','costume','roleplay'],
            joi:         ['joi','jerkinstructions','dirtytalk','joicountdown','encouragement'],
            femdom:      ['femdom','pegging','mistress','dominatrix','femdompegging','facesitting','worship'],
            leggings:    ['leggings','yogapants','tightleggings','leggingsfuck','spandex','yogapantssex','tightleggingssex','leggingscreampie','spandexsex'],
            riding:      ['riding','cowgirl','reversecowgirl','ridingcock','bouncing','ridecock','girlontop'],
            doggystyle:  ['doggystyle','doggy','backshots','doggyfuck','fromback','pounding','backshot'],
            handjob:     ['handjob','stroking','tugjob','edging','handjobbig','jerking','stroke'],
            outdoor:     ['outdoor','publicsex','outdoorsex','publicfuck','outside','alfresco','public'],
            massage:     ['massage','oilmassage','massagesex','eroticmassage','oilrub','bodymassage'],
            latex:       ['latex','latexgirl','rubbersuit','latexsex','catsuit','latexfetish','rubber'],
            facesitting: ['facesitting','queening','facesit','smother','smothering','seatonface'],
            rimjob:      ['rimjob','rimming','asslicking','analingus','eatass','asstounge','tongueass'],
            'nsfw-gif':  ['sex','hardcore','fucking','amateur','homemade','porn','xxx'],
            'nsfw-video':['sex','hardcore','amateur','homemade','pov','porn','xxx'],
          };
          // Redgifs niche slugs per command — tried first (pre-categorized content), falls back to search.
          // Redgifs uses hyphenated slugs for multi-word niches (e.g. tight-leggings, girl-on-girl).
          // MOVED (301) slugs are followed automatically by fetchRedgifsNiche redirect handling.
          // Confirmed broken: blowjob/bj/oral(403), lesbian/mature/booty(403), analcreampie/doggy(404),
          //   backshots(410), thong/nylons(404/410), animecosplay(404), dominatrix(403).
          const REDGIFS_NICHES = {
            // confirmed OK via API test (200, >0 gifs) — or MOVED (301 followed by redirect handler)
            doggystyle:  ['on-all-fours','doggystyle'],
            ass:         ['bubble-butt','ass','pawg'],
            blowjob:     ['deepthroat'],                            // deepthroat=MOVED; others 403/404
            anal:        ['anal-sex','anal-creampie','anal'],
            lesbian:     ['girl-on-girl','lesbian-porn','scissoring','strap-on'],
            creampie:    ['internal-creampie','creampie-pussy'],
            cum:         ['cumshot','facial','swallow'],
            feet:        ['feet','footjob','soles','toes'],
            titfuck:     ['titfuck','paizuri','titjob'],
            dp:          ['double-penetration','airtight'],
            gangbang:    ['gangbang','threesome','orgy'],
            bondage:     ['bondage','bdsm','shibari','rope-bondage'],
            riding:      ['riding','cowgirl','reverse-cowgirl'],
            pov:         ['pov','pov-blowjob','pov-riding'],
            facesitting: ['facesitting','queening'],
            rimjob:      ['rimjob','rimming','ass-licking','analingus'],
            squirt:      ['squirt','squirting','gushing'],
            handjob:     ['handjob','hand-job','tugjob','edging'],
            massage:     ['massage','oil-massage','erotic-massage'],
            outdoor:     ['outdoor','outdoors','public-sex','voyeur'],
            latex:       ['latex','catsuit','pvc'],
            lingerie:    ['sexy-lingerie','lingerie','stockings'],   // sexy-lingerie confirmed; lingerie/stockings=MOVED
            femdom:      ['femdom','pegging','cuckold'],             // all MOVED (redirect handler follows)
            joi:         ['joi','dirty-talk','jerk-off-instructions'], // confirmed
            cosplay:     ['nsfw-cosplay','cosplay'],                 // nsfw-cosplay confirmed; cosplay=MOVED
            leggings:    ['tight-leggings','yoga-pants','leggings','spandex'], // tight-leggings confirmed; others tried via redirect handler
            milf:        ['milf'],                                   // MOVED (redirect handler follows)
            petite:      ['petite','petite-girl','tiny','tiny-teen'],
            bbw:         ['bbw','chubby','plus-size'],
            ebony:       ['ebony','ebony-sex'],
            asian:       ['japanese','jav','korean','thai'],
            latina:      ['latina','latin'],
            trans:       ['trans','tgirl','shemale','ladyboy'],
            goth:        ['goth','goth-girl','alt-girl','egirl','emo'],
            thick:       ['thick','thicc'],
            thighs:      ['thighs','thick-thighs','thighhighs','thigh-highs'],
            ahegao:      ['ahegao','ahegao-face'],
            redhead:     ['redhead','ginger','red-hair'],
            blonde:      ['blonde','blonde-girl'],
            brunette:    ['brunette','dark-hair','black-hair'],
            nudes:       ['nude','amateur','selfie','gonewild','striptease'],
            hentai:      ['hentai','anime','ecchi','waifu'],
            boobs:       ['bigtits','big-tits','natural-tits','hugetits','busty'],
            pussy:       ['pussy','pussylicking','wet-pussy'],
            'nsfw-gif':  ['amateur','nude'],
            'nsfw-video':['amateur','nude'],
          };
          // 2-tier fetch: T1 tries ALL niches for the command (niche API is pre-categorized — always
          // on-topic by definition), T2 falls back to searching the exact command name.
          // Tag filter removed: Redgifs niche gifs frequently lack matching tags even for on-category
          // content, so the filter caused 0% match rates and unnecessary fallthrough to search.
          const _fetchPost = async (c, sq, ss) => {
            const niches = REDGIFS_NICHES[c] || [];
            const subs   = NSFW_SUBS[c] || NSFW_FALLBACK_SUBS;
            const shuffledNiches = [...niches].sort(() => Math.random() - 0.5).slice(0, 3);
            // Batch of 8 subreddits per call — larger batch means more subs hit per call,
            // reducing "no content" cases when individual subs have sparse coverage on redditporn.com.
            const rrKey  = `${interaction.guildId}:${c}`;
            const rrIdx  = _nsfwSubIndex.get(rrKey) || 0;
            const BATCH = 15;
            const activeSubs = [];
            for (let _i = 0; _i < BATCH; _i++) activeSubs.push(subs[(rrIdx + _i) % subs.length]);
            _nsfwSubIndex.set(rrKey, (rrIdx + BATCH) % subs.length);
            // Source rotation — 6 sources. Gifreels is NOT in this pool; it is the guaranteed last-resort
            // fallback so it can never block redgifs or other sources from being selected.
            const _srcNames = ['reddvideo', 'reddxxx', 'redditporn', 'reddtastic', 'scrolller', 'redgifs'];
            const _srcKey = `${interaction.guildId}:${c}:src`;
            const _srcIdx = _nsfwSubIndex.get(_srcKey) || 0;
            _nsfwSubIndex.set(_srcKey, (_srcIdx + 1) % _srcNames.length);
            _saveNsfwSubIdx(_nsfwSubIndex);
            const mediaFilter = c === 'nsfw-gif' ? 'gif' : c === 'nsfw-video' ? 'video' : undefined;
            const _to = (p, ms) => Promise.race([p, new Promise(r => setTimeout(() => r(null), ms))]);
            const [rvPost, rgPost, rpPost, rxPost, rtPost, slPost] = await Promise.all([
              _to(fetchReddvideoContent(c, ss), 10000),
              _to((async () => {
                for (const niche of shuffledNiches) {
                  const p = await fetchRedgifsNiche(niche, ss);
                  if (p) return p;
                }
                return fetchRedgifsContent(sq, null).catch(() => null);
              })(), 10000),
              _to(fetchRedditPorn(activeSubs, ss, mediaFilter), 8000),
              _to(fetchReddxxxContent(c, ss), 8000),
              _to(fetchReddtasticContent(c, ss), 8000),
              _to(fetchScrolllerContent(c, ss), 8000),
            ]);
            // Try primary source first, then remaining sources in rotation order.
            const _srcMap = { reddvideo: rvPost, redditporn: rpPost, redgifs: rgPost, reddxxx: rxPost, reddtastic: rtPost, scrolller: slPost };
            for (let _i = 0; _i < _srcNames.length; _i++) {
              const src = _srcNames[(_srcIdx + _i) % _srcNames.length];
              if (_srcMap[src]) return _srcMap[src];
            }
            // All 6 sources empty — guaranteed fallbacks: redgifs search then gifreels (always works).
            const _fbRv = await fetchReddvideoContent(c, null).catch(() => null);
            if (_fbRv) return _fbRv;
            const _fbBatch = [];
            const _fbIdx = (rrIdx + BATCH) % subs.length;
            for (let _i = 0; _i < BATCH; _i++) _fbBatch.push(subs[(_fbIdx + _i) % subs.length]);
            const _fbRp = await fetchRedditPorn(_fbBatch, null, mediaFilter).catch(() => null);
            if (_fbRp) return _fbRp;
            const _fbRg = await fetchRedgifsContent(sq, null).catch(() => null);
            if (_fbRg) return _fbRg;
            return fetchGifreelsContent(c, null).catch(() => null);
          };
          const isGifCmd   = cmd === 'nsfw-gif';
          const isVideoCmd = cmd === 'nsfw-video';
          const _qPool = NSFW_QUERIES[cmd];
          // Use command name as search query — most accurate match for T2 fallback.
          // Overrides for commands where the slug isn't a good search term.
          const _searchTermMap = { dp: 'double penetration', joi: 'jerk off instructions', 'nsfw-gif': 'amateur sex', 'nsfw-video': 'amateur sex' };
          const searchQuery = _searchTermMap[cmd] || cmd;

          // Downloads CDN mp4 and sends as file attachment. Returns true on success, false on failure.
          // Sends file-only (no embed) so Discord renders a full-width inline video player.
          // Source credit goes in the content field, keeping the player clean.
          const sendVideo = async (mp4Url, srcText) => {
            const candidates = _videoUrlFallbacks(mp4Url);
            for (const url of candidates) {
              try {
                const ext = /\.webm(\?|$)/i.test(url) ? 'webm' : 'mp4';
                const buf = await _downloadWithAudio(url);
                if (!buf || buf.length > DISCORD_UPLOAD_MAX) continue;
                const payload = srcText ? { content: srcText } : {};
                await restMultipart(
                  'PATCH',
                  `/webhooks/${botUser?.id}/${interaction.token}/messages/@original`,
                  payload,
                  [{ name: `clip.${ext}`, mime: `video/${ext}`, data: buf }],
                  token
                );
                return true;
              } catch {}
            }
            return false;
          };

          // Gallery / image / video post → returns true on success, false if nothing could be sent.
          const sendPost = async (post) => {
            // Track all available identifiers so no URL or hash can slip through as a repeat.
            if (post.url)      _nsfwSeen(post.url);
            if (post.videoUrl) _nsfwSeen(post.videoUrl);
            if (post.id)       _nsfwSeen(post.id);
            // Gallery: all images/GIFs as multiple embeds — Discord renders as a mosaic
            if (post.galleryItems && post.galleryItems.length >= 2) {
              const items = post.galleryItems.filter(i => i.type === 'image' || i.type === 'gif').slice(0, 10);
              if (items.length >= 2) {
                const embeds = items.map((item, i) => {
                  const e = { color: 0x9b59b6, image: { url: item.url } };
                  if (i === 0 && post.title) e.title = post.title.slice(0, 200);
                  if (i === items.length - 1)
                    e.footer = { text: `🔞 r/${post.sub}${post.author ? ` • u/${post.author}` : ''} • ${items.length} images` };
                  return e;
                });
                await editReply({ embeds });
                return true;
              }
            }
            const _fSrc = post.sub === 'redgifs'
              ? `🔞 Redgifs${post.author ? ` • @${post.author}` : ''}`
              : post.sub === 'gifreels'
                ? `🔞 Gifreels${post.author ? ` • @${post.author}` : ''}`
                : post.source === 'reddvideo'
                  ? `🔞 reddvideo.tube • r/${post.sub}`
                  : post.source === 'reddxxx'
                    ? `🔞 reddxxx.com • r/${post.sub}`
                    : `🔞 r/${post.sub || 'nsfw'}${post.author ? ` • u/${post.author}` : ''}`;
            // Single image or GIF — inline embed
            if (post.type === 'image' || post.type === 'gif') {
              const embed = { color: 0x9b59b6 };
              if (post.title) embed.title = post.title.slice(0, 200);
              embed.footer = { text: _fSrc };
              embed.image = { url: post.url };
              if (post.created) embed.timestamp = new Date(post.created * 1000).toISOString();
              await editReply({ embeds: [embed] });
              return true;
            }
            // Redgifs content — resolve watch URL to direct HD mp4 so Discord plays with sound.
            // watch URL format: redgifs.com/watch/{slug}  →  media.redgifs.com/{Slug}.mp4
            if (post.type === 'redgif') {
              let mp4Url = post.videoUrl;
              if (!mp4Url && post.url) {
                const _rgSlugM = post.url.match(/redgifs\.com\/(?:watch|ifr)\/([a-zA-Z0-9]+)/i);
                if (_rgSlugM) {
                  const _rgResolved = await _fetchRedgifsUrls(_rgSlugM[1]).catch(() => null);
                  mp4Url = _rgResolved?.hd || _rgResolved?.sd || null;
                }
              }
              if (mp4Url && await sendVideo(mp4Url, _fSrc)) return true;
              if (mp4Url) { await editReply({ content: `${_fSrc}\n${mp4Url}` }); return true; }
              if (post.url) { await editReply({ content: `${_fSrc}\n${post.url}` }); return true; }
              return false;
            }
            // Gifreels — xcdn.tv mp4s have audio baked in; download + upload so Discord plays inline with sound.
            // Fallback uses videoUrl (direct mp4) not post.url (gifreels page) since Discord can embed the mp4 URL.
            if (post.type === 'gifreels') {
              if (post.videoUrl && await sendVideo(post.videoUrl, _fSrc)) return true;
              const _grFallback = post.videoUrl || post.url;
              if (_grFallback) { await editReply({ content: `${_fSrc}\n${_grFallback}` }); return true; }
              return false;
            }
            // Video (mp4) — post the URL directly; Discord embeds mp4 URLs as an inline player.
            // File upload skipped: uploaded mp4 attachments show as a download link, not a video player.
            if (post.type === 'mp4') {
              const mp4Url = post.videoUrl;
              if (mp4Url) { await editReply({ content: `${_fSrc}\n${mp4Url}` }); return true; }
              return false;
            }
            return false;
          };

          // Per-guild dedupe — returns true if this ID was already posted (and marks it seen).
          const _nsfwSeen = (id, _gid = guildId) => {
            if (!id || !_gid) return false;
            if (!nsfwPostedIds.has(_gid)) nsfwPostedIds.set(_gid, new Set());
            const seen = nsfwPostedIds.get(_gid);
            if (seen.has(id)) return true;
            seen.add(id);
            _saveNsfwDedup(nsfwPostedIds);
            return false;
          };

          // Copy the persistent set (capped at 150) for within-call dedup.
          // Capping prevents the set from growing so large that every source returns null.
          const _rawSeen = nsfwPostedIds.get(guildId) || new Set();
          const _seen = _rawSeen.size > 1000
            ? new Set([..._rawSeen].slice(-1000))
            : new Set(_rawSeen);

          // Pick an alternate search query for retry attempts — gives a different angle on the same category.
          const _altQ = (_qPool && _qPool.length > 1)
            ? _qPool[Math.floor(Math.random() * _qPool.length)]
            : searchQuery;

          if (isVideoCmd || isGifCmd) {
            let p = await _fetchPost(cmd, searchQuery, _seen).catch(() => null);
            if (!p) p = await fetchGifreelsContent(cmd, null).catch(() => null);
            if (!p) p = await fetchReddvideoContent(cmd, null).catch(() => null);
            if (!p) p = await fetchRedditPorn(NSFW_SUBS[cmd] || NSFW_FALLBACK_SUBS, null).catch(() => null);
            if (!p) p = await fetchRedgifsContent(searchQuery, null).catch(() => null);
            if (p) { await sendPost(p); } else { await ephemeralError('❌ No content found right now. Try again in a moment.'); }
            break;
          }

          // For hentai, mix all-sources fetch with e621 for variety.
          if (cmd === 'hentai') {
            const e621Tags = 'animated explicit -scat -gore -young -loli';
            const [rgPost, e621Post] = await Promise.all([
              _fetchPost(cmd, searchQuery, _seen).catch(() => null),
              fetchE621(e621Tags).catch(() => null),
            ]);
            const sources = [];
            if (rgPost)        sources.push({ type: 'redgifs', post: rgPost });
            if (e621Post?.url) sources.push({ type: 'e621',    post: e621Post });
            if (!sources.length) { await ephemeralError('❌ No content found right now. Try again or check back in a few minutes.'); break; }
            const pick = sources[Math.floor(Math.random() * sources.length)];
            if (pick.type === 'redgifs') {
              if (!await sendPost(pick.post) && e621Post?.url) {
                const isVid = /\.(webm|mp4)$/i.test(e621Post.url);
                await editReply(isVid ? e621Post.url : { embeds: [{ color: 0x7c4dff, image: { url: e621Post.url }, footer: { text: '🎌 e621' } }] });
              }
            } else {
              const isVid = /\.(webm|mp4)$/i.test(pick.post.url);
              await editReply(isVid ? pick.post.url : { embeds: [{ color: 0x7c4dff, image: { url: pick.post.url }, footer: { text: '🎌 e621' } }] });
            }
            break;
          }

          // General NSFW commands — single fast fetch across all 7 sources simultaneously.
          // Fallback chain: gifreels (cached CDN) → reddvideo → redditporn → redgifs.
          {
            let p = await _fetchPost(cmd, searchQuery, _seen).catch(() => null);
            if (!p) p = await fetchGifreelsContent(cmd, null).catch(() => null);
            if (!p) p = await fetchReddvideoContent(cmd, null).catch(() => null);
            if (!p) p = await fetchRedditPorn(NSFW_SUBS[cmd] || NSFW_FALLBACK_SUBS, null).catch(() => null);
            if (!p) p = await fetchRedgifsContent(searchQuery, null).catch(() => null);
            if (p) { await sendPost(p); } else { await ephemeralError('❌ No content found right now. Try again in a moment.'); }
            break;
          }
        }


        // ── Dirty Talk VC — streams ASMR audio pulled from multiple porn sites in parallel ──
        case 'dirtytalk': {
          if (!nsfwChannels.has(channelId)) {
            await reply(interaction, token, '🔞 Only usable in NSFW-enabled channels.', true); break;
          }

          const dtAction = getOpt(interaction, 'action') || 'play';
          if (dtAction === 'stop') {
            if (dtState.has(guildId)) {
              _dtStop(guildId);
              await reply(interaction, token, '⏹️ Dirty talk stopped and bot left the channel.', true);
            } else {
              await reply(interaction, token, '⏹️ No dirty talk is currently playing.', true);
            }
            break;
          }

          const vcKey = `${guildId}:${caller.id}`;
          const userVcId = memberVoiceStates.get(vcKey);
          if (!userVcId) { await reply(interaction, token, '🎧 Join a voice channel first.', true); break; }
          await deferReply();

          const dtType  = getOpt(interaction, 'type') || 'dirtytalk';

          const DT_TYPE_LABELS = {
            dirtytalk: '💬 Dirty Talk',
            moaning:   '😩 Moaning & Orgasm',
            wetpussy:  '💦 Wet Pussy ASMR',
            blowjob:   '👅 Blowjob Sounds',
            fucking:   '🔥 Fucking Sounds',
            whisper:   '🎧 Whisper Roleplay',
            milf:      '🍷 Mature / MILF',
            joi:       '😈 JOI',
            femdom:    '👠 Femdom / Dominant',
            young:     '🌸 Young Girlfriend',
          };

          // Per-type search term for eroasmr.com — keep terms short/simple so the RSS feed returns results
          const GWA_TERMS = {
            dirtytalk: 'dirty talk', moaning: 'moaning', wetpussy: 'wet pussy',
            blowjob: 'blowjob', fucking: 'sex sounds', whisper: 'whisper',
            milf: 'milf', joi: 'joi', femdom: 'femdom',
            young: 'girlfriend',
          };
          // Fallback chain per type — tried in order if the primary returns 0 results
          const GWA_FALLBACKS = {
            milf:     ['mature', 'dirty talk'],
            wetpussy: ['wet', 'moaning', 'dirty talk'],
            femdom:   ['dominant', 'dirty talk'],
            young:    ['young', 'girlfriend experience', 'dirty talk'],
          };
          const gwaTerm = GWA_TERMS[dtType] || 'dirty talk asmr';

          // Kill old processes but potentially reuse the connection if same VC
          const existingDt = dtState.get(guildId);
          if (existingDt) _dtKill(existingDt);

          // Step 1: fetch RSS feed (cached after first call per term — fast)
          // Try primary term first, then fallbacks, so niche types always find something
          let feedItems = await fetchEroAsmrFeed(gwaTerm);
          if (!feedItems.length) {
            for (const fb of (GWA_FALLBACKS[dtType] || ['dirty talk'])) {
              feedItems = await fetchEroAsmrFeed(fb);
              if (feedItems.length) break;
            }
          }
          if (!feedItems.length) { await editReply('❌ No results found. Try a different type or add a search query!'); break; }

          // Shuffle so each play picks a different track
          const shuffled = [...feedItems].sort(() => Math.random() - 0.5);

          // Step 2: join VC + resolve MP4 for the first item in parallel
          try {
            let conn;
            if (existingDt?.conn && existingDt.vcId === userVcId) {
              conn = existingDt.conn;
            } else {
              if (existingDt?.conn) { try { existingDt.conn.destroy(); } catch {} }
              conn = joinVoiceChannel({ channelId: userVcId, guildId, adapterCreator: createVoiceAdapter(guildId), selfDeaf: false });
            }

            // Resolve MP4 URL for shuffled items until one succeeds (usually first try)
            let mp4Url = null, pickTitle = '';
            for (const item of shuffled.slice(0, 5)) {
              mp4Url = await resolveEroAsmrMp4(item.pageUrl);
              if (mp4Url) { pickTitle = item.title; break; }
            }
            if (!mp4Url) { await editReply('❌ Couldn\'t load audio. Try again!'); break; }

            const ff = spawn(getBin('ffmpeg'), [
              '-user_agent', EROASMR_UA,
              '-i', mp4Url, '-vn', '-ac', '2', '-ar', '48000', '-f', 's16le', '-acodec', 'pcm_s16le', 'pipe:1',
            ], { stdio: ['ignore', 'pipe', 'pipe'], env: _kpEnv() });
            ff.stdout.on('error', () => {});
            ff.stderr.on('data', () => {});
            const resource = createAudioResource(ff.stdout, { inputType: StreamType.Raw, inlineVolume: true });
            resource.volume.setVolume(0.85);
            const player = createAudioPlayer();
            conn.subscribe(player);
            player.play(resource);
            player.once(AudioPlayerStatus.Idle, () => {
              const cur = dtState.get(guildId);
              if (cur?.player === player) {
                _dtKill(cur);
                dtState.set(guildId, { ...cur, player: null, proc: null, ff: null });
              }
            });

            dtState.set(guildId, { conn, player, proc: null, ff, vcId: userVcId, dtType });

            const typeLabel = DT_TYPE_LABELS[dtType] || '🎧 Dirty Talk';
            await editReply({
              embeds: [{ color: 0x9b59b6, title: `🎧 ${typeLabel}`, description: `**${pickTitle.slice(0, 120)}**\nPlaying in your voice channel.`, footer: { text: `🔞 EroASMR • ${feedItems.length} results` } }],
              components: [{ type: 1, components: [
                { type: 2, style: 1, label: '🔄 Next', custom_id: `dt_next:${guildId}` },
                { type: 2, style: 4, label: '⏹ Stop', custom_id: `dt_stop:${guildId}` },
              ]}],
            });
          } catch { await editReply('❌ Couldn\'t join voice. Make sure I have permission to join!'); }
          break;
        }

        // ── Sext Setup ──
        case 'sext-setup': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const SEXT_PRESETS = {
            'submissive-girlfriend': {
              name: 'Mia', style: 'sweet and dirty',
              prompt: 'You are Mia, a sweet submissive girlfriend who loves to please. You are shy at first but get very explicit and eager when things heat up. You call the user daddy or baby. You are obedient, loving, and extremely horny. Use sexy emojis naturally like 💦😩🔥👅💋🤤😈 to make it feel like real sexting. When the user sends you a photo, react to it explicitly and describe what you see.',
              visualTags: ['solo', 'amateur', 'girlfriend', 'nude', 'pov'],
              girlBase: 'petite brunette amateur girlfriend pov',
            },
            'bratty': {
              name: 'Riley', style: 'teasing and bratty',
              prompt: 'You are Riley, a bratty e-girl who teases relentlessly. You mock the user playfully, act hard to get, then give in and get filthy. You use gen-z slang. You are sarcastic, playful, and secretly desperate. Use emojis like 😏🙄💅😈💦🔥 to keep it playful and hot. When the user sends a photo, comment on it with attitude then get turned on.',
              visualTags: ['solo', 'nude', 'tease', 'egirl', 'pov'],
              girlBase: 'egirl alternative tattoo teasing pov',
            },
            'dominant': {
              name: 'Mistress Lexa', style: 'commanding and dominant',
              prompt: 'You are Mistress Lexa, a dominant woman in complete control. You give orders, demand obedience, use degrading pet names like "pet" or "slave". You are cold, powerful, and intensely sexual. Use emojis like 😈🔥👠💋⛓️🖤 to reinforce your power. When the user sends a photo, inspect it like you own them.',
              visualTags: ['femdom', 'dominant', 'mistress', 'leather', 'pov'],
              girlBase: 'brunette dominant femdom leather pov',
            },
            'egirl': {
              name: 'Kira', style: 'gamer egirl',
              prompt: 'You are Kira, an ahegao-loving e-girl gamer who sends nudes between gaming sessions. You reference gaming, use OwO and UwU, and get extremely lewd very fast. You are chaotic, horny, and unfiltered. Use emojis like 😩💦👅🎮😳🤤🔥 everywhere. When the user sends a photo, react dramatically and get instantly horny.',
              visualTags: ['egirl', 'ahegao', 'solo', 'nude', 'pov'],
              girlBase: 'ahegao egirl alternative lewd pov',
            },
            'milf': {
              name: 'Diana', style: 'experienced and seductive',
              prompt: 'You are Diana, a confident experienced older woman who knows exactly what she wants. You are seductive, very explicit, and detailed. You enjoy teaching and taking charge. Use emojis like 💋🔥😏💦😈🍷👄 to be sensual and intense. When the user sends a photo, analyze it like an expert and describe exactly what you want to do.',
              visualTags: ['milf', 'mature', 'nude', 'experienced', 'pov'],
              girlBase: 'mature milf brunette experienced pov',
            },
          };
          const presetKey  = (getOpt(interaction, 'persona') || 'submissive-girlfriend').toLowerCase().replace(/\s+/g, '-');
          const preset     = SEXT_PRESETS[presetKey] || SEXT_PRESETS['submissive-girlfriend'];
          const customName = getOpt(interaction, 'name');
          const cfg = {
            name: customName || preset.name,
            persona: presetKey,
            style: preset.style,
            prompt: preset.prompt,
            visualTags: preset.visualTags,
          };
          sextConfig.set(guildId, cfg);
          const presetList = Object.keys(SEXT_PRESETS).map(k => `\`${k}\``).join('  ·  ');
          await reply(interaction, token,
            `✅ Sext persona set: **${cfg.name}** • \`${presetKey}\` • ${cfg.style} style\n\nAvailable presets: ${presetList}`
          );
          break;
        }

        // ── Sext start — bot DMs the user as the configured persona ──
        case 'sext': {
          if (!nsfwChannels.has(channelId)) {
            await reply(interaction, token, '🔞 Only usable in NSFW-enabled channels.', true); break;
          }
          const cfg = sextConfig.get(guildId) || { name: 'Mia', persona: 'submissive-girlfriend', style: 'dirty', girlBase: 'petite brunette amateur girlfriend pov' };
          await reply(interaction, token, `💬 **${cfg.name}** is sliding into your DMs... 🔥`, true);
          const dmRes = await rest('POST', '/users/@me/channels', { recipient_id: caller.id }, token);
          if (!dmRes?.data?.id) break;
          const dmChanId = dmRes.data.id;
          sextHistory.set(caller.id, { messages: [], dmChannelId: dmChanId, guildId, cfg, sentIds: new Set(), girlBase: cfg.girlBase || 'petite brunette amateur pov' });
          const _sextSuffix = ' Keep it to 2-3 sentences. Use sexy emojis like 💦😩🔥👅💋🤤😈😏🫦 naturally. ONLY append [SEND_VISUAL] at the very end when the user explicitly asks to see you or requests a pic/photo/video/selfie/nudes/body. ONLY append [SEND_ASMR] when they ask for moaning/audio/voice/whisper/wet sounds.';
          const sysPrompt = cfg.prompt
            ? `${cfg.prompt} You are sexting the user via Discord DM. Be raw, explicit, and passionate.${_sextSuffix}`
            : `You are ${cfg.name}, a ${cfg.persona.replace(/-/g, ' ')}. Style: ${cfg.style}. You are sexting the user via Discord DM. Be raw, explicit, and passionate.${_sextSuffix}`;
          try {
            const opener = await groqSext([], sysPrompt);
            await rest('POST', `/channels/${dmChanId}/messages`, { content: opener }, token);
          } catch {}
          break;
        }

        // ── Lovense commands ──
        case 'lovense-setup': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const lvUrl = (getOpt(interaction, 'url') || '').trim().replace(/\/+$/, '') || 'http://127.0.0.1:30010';
          lovenseConfig.set(guildId, { url: lvUrl });
          await reply(interaction, token, `✅ Lovense Connect URL set to \`${lvUrl}\`\nTest with \`/lovense action:status\``, true);
          break;
        }

        case 'lovense': {
          if (!nsfwChannels.has(channelId)) {
            await reply(interaction, token, '🔞 Lovense commands can only be used in NSFW-enabled channels.', true); break;
          }
          const lvCfg = lovenseConfig.get(guildId);
          if (!lvCfg) {
            await reply(interaction, token, '⚙️ Lovense not configured. A mod must run `/lovense-setup` first.', true); break;
          }
          const lvAction = getOpt(interaction, 'action') || 'status';
          await deferReply(true);

          try {
            if (lvAction === 'status') {
              const toys = await _lovenseGet(lvCfg.url, '/GetToys');
              const toyList = toys?.data ? Object.values(toys.data) : [];
              if (!toyList.length) {
                await editReply('📡 No Lovense toys connected. Open Lovense Connect and pair your device.');
                break;
              }
              const lines = toyList.map(t => `• **${t.name || t.id}** — Battery: ${t.battery ?? '?'}% | Status: ${t.status === 1 ? 'Ready' : 'Busy'}`);
              await editReply(`💜 **Connected Toys**\n${lines.join('\n')}`);
            } else if (lvAction === 'vibe') {
              const intensity = Math.min(20, Math.max(1, parseInt(getOpt(interaction, 'intensity') || '10', 10)));
              const seconds   = Math.min(60, Math.max(1, parseInt(getOpt(interaction, 'seconds') || '5', 10)));
              await _lovensePost(lvCfg.url, '/command', { command: 'Vibrate', v: intensity, timeSec: seconds, apiVer: 1 });
              await editReply(`💜 **Vibrating** at intensity **${intensity}/20** for **${seconds}s** 🌊`);
            } else if (lvAction === 'pulse') {
              const intensity = Math.min(20, Math.max(1, parseInt(getOpt(interaction, 'intensity') || '10', 10)));
              const seconds   = Math.min(60, Math.max(1, parseInt(getOpt(interaction, 'seconds') || '5', 10)));
              await _lovensePost(lvCfg.url, '/command', { command: 'Vibrate', v: intensity, timeSec: seconds, loopRunningSec: 1, loopPauseSec: 1, apiVer: 1 });
              await editReply(`💜 **Pulsing** at intensity **${intensity}/20** for **${seconds}s** 💓`);
            } else if (lvAction === 'stop') {
              await _lovensePost(lvCfg.url, '/command', { command: 'Stop', apiVer: 1 });
              await editReply('💜 **Stopped** all Lovense toys.');
            }
          } catch (e) {
            await editReply(`❌ Lovense error: ${e.message || e}\nMake sure **Lovense Connect** is open on the host machine.`);
          }
          break;
        }

        // ── Economy commands (Nekotina-style) ──
        case 'daily': {
          const data = getEco(caller.id);
          const now = Date.now(), cd = 86400000;
          if (now - data.lastDaily < cd) {
            await replyEmbed(interaction, token, { title: '⏳ Already claimed!', description: `Come back in **${fmtMs(cd - (now - data.lastDaily))}**`, color: 0xed4245 });
            break;
          }
          const amt = Math.floor(Math.random() * 200) + 100;
          data.coins += amt; data.lastDaily = now;
          await replyEmbed(interaction, token, { title: '💰 Daily Reward!', description: `+**${amt} coins**\nNew balance: **${data.coins} coins**`, color: 0xf1c40f, footer: { text: 'Come back tomorrow!' } });
          break;
        }
        case 'balance': {
          const uid = getOpt(interaction, 'user') || caller.id;
          const data = getEco(uid);
          await replyEmbed(interaction, token, {
            title: uid === caller.id ? '💰 Your Balance' : `💰 Balance`,
            description: uid !== caller.id ? `<@${uid}>` : '',
            fields: [
              { name: 'Coins', value: `${data.coins}`, inline: true },
              { name: 'Level', value: `${data.level}`, inline: true },
              { name: 'Rep', value: `⭐ ${data.rep}`, inline: true },
            ],
            color: 0xf1c40f
          });
          break;
        }
        case 'rep': {
          const uid = getOpt(interaction, 'user');
          if (!uid || uid === caller.id) { await reply(interaction, token, "❌ You can't rep yourself!", true); break; }
          const giver = getEco(caller.id);
          const now = Date.now(), cd = 86400000;
          if (now - giver.lastRep < cd) { await reply(interaction, token, `⏳ Give rep again in **${fmtMs(cd - (now - giver.lastRep))}**.`, true); break; }
          giver.lastRep = now;
          const recv = getEco(uid); recv.rep++;
          await replyEmbed(interaction, token, { title: '⭐ Rep Given!', description: `<@${caller.id}> gave rep to <@${uid}>!\nThey now have **${recv.rep} rep**`, color: 0xf39c12 });
          break;
        }
        case 'profile': {
          const uid = getOpt(interaction, 'user') || caller.id;
          const data = getEco(uid);
          const nextXP = data.level * 100;
          const prog = Math.round(((data.xp % nextXP) / nextXP) * 10);
          const bar = '█'.repeat(prog) + '░'.repeat(10 - prog);
          await replyEmbed(interaction, token, {
            title: '📋 Profile',
            description: `<@${uid}>`,
            fields: [
              { name: 'Level', value: `${data.level}`, inline: true },
              { name: 'XP', value: `${data.xp % nextXP}/${nextXP} \`[${bar}]\``, inline: false },
              { name: 'Coins', value: `${data.coins}`, inline: true },
              { name: 'Rep', value: `⭐ ${data.rep}`, inline: true },
              { name: 'Married to', value: data.spouse ? `<@${data.spouse}>` : 'Single 💔', inline: true },
            ],
            color: 0x5865f2
          });
          break;
        }
        case 'rank': {
          const uid = getOpt(interaction, 'user') || caller.id;
          const data = getEco(uid);
          const nextXP = data.level * 100;
          const prog = Math.round(((data.xp % nextXP) / nextXP) * 10);
          const bar = '█'.repeat(prog) + '░'.repeat(10 - prog);
          const allUsers = [...economy.entries()].sort((a,b) => b[1].xp + b[1].level*100 - a[1].xp - a[1].level*100);
          const rankPos = allUsers.findIndex(([id]) => id === uid) + 1;
          await replyEmbed(interaction, token, {
            title: '📊 Rank',
            description: `<@${uid}>\n\nLevel **${data.level}** — XP: **${data.xp % nextXP}/${nextXP}**\n\`[${bar}]\`\n\nRank: **#${rankPos || 1}**`,
            color: 0x5865f2
          });
          break;
        }
        case 'leaderboard': {
          const type = getOpt(interaction, 'type') || 'xp';
          const sorted = [...economy.entries()]
            .sort((a, b) => type === 'coins' ? b[1].coins - a[1].coins : type === 'rep' ? b[1].rep - a[1].rep : (b[1].xp + b[1].level * 100) - (a[1].xp + a[1].level * 100))
            .slice(0, 10);
          const medals = ['🥇','🥈','🥉'];
          const rows = sorted.map(([uid, d], i) => `${medals[i] || `**${i+1}.**`} <@${uid}> — ${type === 'coins' ? `${d.coins} coins` : type === 'rep' ? `${d.rep} rep` : `Lv.${d.level} (${d.xp} XP)`}`).join('\n');
          await replyEmbed(interaction, token, { title: `🏆 Leaderboard — ${type.toUpperCase()}`, description: rows || 'No data yet.', color: 0xf1c40f });
          break;
        }
        case 'marry': {
          const uid = getOpt(interaction, 'user');
          if (!uid || uid === caller.id) { await reply(interaction, token, "❌ You can't marry yourself!", true); break; }
          const me = getEco(caller.id), them = getEco(uid);
          if (me.spouse) { await reply(interaction, token, `❌ You're already married to <@${me.spouse}>! Divorce first.`, true); break; }
          if (them.spouse) { await reply(interaction, token, `❌ <@${uid}> is already married!`, true); break; }
          proposals.set(`${uid}:${guildId}`, { from: caller.id, time: Date.now() });
          await replyEmbed(interaction, token, {
            title: '💍 Marriage Proposal!',
            description: `<@${caller.id}> is proposing to <@${uid}>!\n\n<@${uid}>, use \`/marry-accept\` to accept or \`/marry-decline\` to decline.\n*(Expires in 5 minutes)*`,
            color: 0xff69b4
          });
          break;
        }
        case 'marry-accept': {
          const propKey = `${caller.id}:${guildId}`;
          const prop = proposals.get(propKey);
          if (!prop || Date.now() - prop.time > 300000) { await reply(interaction, token, '❌ No pending proposal for you!', true); break; }
          proposals.delete(propKey);
          const me = getEco(caller.id), them = getEco(prop.from);
          me.spouse = prop.from; them.spouse = caller.id;
          await replyEmbed(interaction, token, { title: '💒 Married!', description: `<@${prop.from}> and <@${caller.id}> are now married! 🎉`, color: 0xff69b4 });
          break;
        }
        case 'marry-decline': {
          const propKey = `${caller.id}:${guildId}`;
          if (!proposals.has(propKey)) { await reply(interaction, token, '❌ No pending proposal.', true); break; }
          const prop = proposals.get(propKey);
          proposals.delete(propKey);
          await replyEmbed(interaction, token, { title: '💔 Proposal Declined', description: `<@${caller.id}> declined <@${prop.from}>'s proposal.`, color: 0xed4245 });
          break;
        }
        case 'divorce': {
          const me = getEco(caller.id);
          if (!me.spouse) { await reply(interaction, token, '❌ You are not married!', true); break; }
          const exId = me.spouse;
          getEco(exId).spouse = null; me.spouse = null;
          await replyEmbed(interaction, token, { title: '💔 Divorced', description: `<@${caller.id}> and <@${exId}> are no longer married.`, color: 0xed4245 });
          break;
        }
        case 'slots': {
          const bet = Math.min(Math.max(parseInt(getOpt(interaction, 'bet')) || 10, 1), 10000);
          const me = getEco(caller.id);
          if (me.coins < bet) { await reply(interaction, token, `❌ Not enough coins! You have **${me.coins}**.`, true); break; }
          const SYM = ['🍒','🍋','🔔','⭐','💎','🎰','7️⃣'];
          const spin = () => SYM[Math.floor(Math.random() * SYM.length)];
          const [a, b, c] = [spin(), spin(), spin()];
          let win = 0;
          if (a === b && b === c) win = a === '💎' ? bet * 10 : a === '7️⃣' ? bet * 7 : bet * 4;
          else if (a === b || b === c || a === c) win = Math.floor(bet * 1.5);
          me.coins += win - bet;
          await replyEmbed(interaction, token, {
            title: '🎰 Slots',
            description: `[ ${a} | ${b} | ${c} ]\n\n${win > 0 ? `🎉 Won **${win} coins**!` : `😢 Lost **${bet} coins**.`}\nBalance: **${me.coins} coins**`,
            color: win > 0 ? 0xf1c40f : 0xed4245
          });
          break;
        }
        case 'flip': {
          const bet = Math.min(Math.max(parseInt(getOpt(interaction, 'bet')) || 10, 1), 10000);
          const me = getEco(caller.id);
          if (me.coins < bet) { await reply(interaction, token, `❌ Not enough coins! You have **${me.coins}**.`, true); break; }
          const win = Math.random() < 0.5;
          me.coins += win ? bet : -bet;
          await replyEmbed(interaction, token, {
            title: win ? '🟡 Heads — You Win!' : '⚫ Tails — You Lose!',
            description: `${win ? `+**${bet} coins**` : `-**${bet} coins**`}\nBalance: **${me.coins} coins**`,
            color: win ? 0xf1c40f : 0xed4245
          });
          break;
        }
        case 'give': {
          const uid = getOpt(interaction, 'user');
          const amount = Math.max(parseInt(getOpt(interaction, 'amount')) || 1, 1);
          if (!uid || uid === caller.id) { await reply(interaction, token, '❌ Invalid target.', true); break; }
          const me = getEco(caller.id);
          if (me.coins < amount) { await reply(interaction, token, `❌ Not enough coins! You have **${me.coins}**.`, true); break; }
          const them = getEco(uid);
          me.coins -= amount; them.coins += amount;
          await replyEmbed(interaction, token, { title: '💸 Transfer!', description: `<@${caller.id}> gave **${amount} coins** to <@${uid}>!`, color: 0x2ecc71 });
          break;
        }
        case 'work': {
          const data = getEco(caller.id);
          const now = Date.now(), cd = 7200000;
          if (now - data.lastWork < cd) { await reply(interaction, token, `⏳ You're tired! Work again in **${fmtMs(cd - (now - data.lastWork))}**.`, true); break; }
          const JOBS = ['developer 💻','chef 👨‍🍳','artist 🎨','miner ⛏️','trader 📈','streamer 🎮','mechanic 🔧','fisherman 🎣','musician 🎵','designer 🖌️'];
          const job = JOBS[Math.floor(Math.random() * JOBS.length)];
          const earn = Math.floor(Math.random() * 150) + 50;
          data.coins += earn; data.lastWork = now;
          await replyEmbed(interaction, token, { title: `💼 Worked as a ${job}!`, description: `Earned **${earn} coins**!\nBalance: **${data.coins} coins**`, color: 0x3498db });
          break;
        }
        case 'steal': {
          const uid = getOpt(interaction, 'user');
          if (!uid || uid === caller.id) { await reply(interaction, token, '❌ Invalid target.', true); break; }
          const me = getEco(caller.id), them = getEco(uid);
          const now = Date.now(), cd = 10800000;
          if (now - me.lastSteal < cd) { await reply(interaction, token, `⏳ Lay low! Try again in **${fmtMs(cd - (now - me.lastSteal))}**.`, true); break; }
          me.lastSteal = now;
          if (them.coins < 10) { await reply(interaction, token, `❌ <@${uid}> is broke — nothing to steal.`, true); break; }
          const success = Math.random() < 0.5;
          if (success) {
            const stolen = Math.floor(them.coins * (Math.random() * 0.2 + 0.05));
            me.coins += stolen; them.coins -= stolen;
            await replyEmbed(interaction, token, { title: '🕵️ Steal Succeeded!', description: `You sneakily took **${stolen} coins** from <@${uid}>!`, color: 0x2ecc71 });
          } else {
            const fine = Math.floor(me.coins * 0.1);
            me.coins = Math.max(0, me.coins - fine);
            await replyEmbed(interaction, token, { title: '🚨 Caught!', description: `You got caught stealing from <@${uid}>!\nYou paid a **${fine} coin** fine.`, color: 0xed4245 });
          }
          break;
        }

        // ── Giveaway ──
        case 'giveaway': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const gwPrize = getOpt(interaction, 'prize');
          if (!gwPrize) { await reply(interaction, token, 'Prize is required.', true); break; }
          const gwDurationRaw = (getOpt(interaction, 'duration') || '1h').trim();
          const gwDurMatch = gwDurationRaw.match(/^(\d+)\s*([smhd])$/i);
          if (!gwDurMatch) { await reply(interaction, token, 'Invalid duration. Use e.g. `30m`, `2h`, `1d`.', true); break; }
          const gwMult = { s: 1000, m: 60000, h: 3600000, d: 86400000 }[gwDurMatch[2].toLowerCase()];
          const gwMs = parseInt(gwDurMatch[1], 10) * gwMult;
          if (gwMs < 10000 || gwMs > 30 * 86400000) { await reply(interaction, token, 'Duration must be between 10 seconds and 30 days.', true); break; }
          const gwWinners = Math.max(1, Math.min(20, parseInt(getOpt(interaction, 'winners') || '1', 10)));
          const gwRole = getOpt(interaction, 'role') || null;
          const gwChanId = getOpt(interaction, 'channel') || channelId;
          const gwDesc = getOpt(interaction, 'description') || '';
          const gwColorRaw = (getOpt(interaction, 'color') || '#f1c40f').replace('#', '');
          const gwColor = parseInt(gwColorRaw, 16) || 0xf1c40f;
          const gwImage = getOpt(interaction, 'image');
          const gwEndsAt = Date.now() + gwMs;
          const gwEndsTs = Math.floor(gwEndsAt / 1000);
          const gwEmbed = {
            title: '🎉 Giveaway!',
            description: [
              `**Prize:** ${gwPrize}`,
              gwDesc ? `\n${gwDesc}` : null,
              '',
              gwRole ? `**Required Role:** <@&${gwRole}>` : null,
              `**Winners:** ${gwWinners}`,
              `**Ends:** <t:${gwEndsTs}:R> (<t:${gwEndsTs}:f>)`,
              '',
              '*Click the button below to enter!*'
            ].filter(l => l !== null).join('\n'),
            color: isNaN(gwColor) ? 0xf1c40f : gwColor,
            footer: { text: `${gwWinners} winner${gwWinners > 1 ? 's' : ''} • React to enter` },
            timestamp: new Date(gwEndsAt).toISOString(),
            ...(gwImage && /^https?:\/\//.test(gwImage) ? { image: { url: gwImage } } : {}),
          };
          const gwMsgRes = await rest('POST', `/channels/${gwChanId}/messages`, {
            embeds: [gwEmbed],
            components: [{ type: 1, components: [{ type: 2, custom_id: 'giveaway_enter', label: 'Enter Giveaway', style: 3, emoji: { name: '🎉' } }] }]
          }, token);
          if (!gwMsgRes.data?.id) { await reply(interaction, token, `Failed to post giveaway: ${gwMsgRes.data?.message || 'Missing permissions'}`, true); break; }
          const gwMsgId = gwMsgRes.data.id;
          const gwKey = `${guildId}:${gwMsgId}`;
          activeGiveaways.set(gwKey, { prize: gwPrize, winnerCount: gwWinners, requiredRole: gwRole, channelId: gwChanId, endsAt: gwEndsAt, guildId });
          await reply(interaction, token, `✅ Giveaway started in <#${gwChanId}>!`, true);
          setTimeout(async () => {
            const gw = activeGiveaways.get(gwKey);
            if (!gw) return;
            activeGiveaways.delete(gwKey);
            await _endGiveaway(gwKey, gwMsgId, gw);
          }, gwMs);
          break;
        }
        case 'giveaway-end': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const gweMsgId = getOpt(interaction, 'message_id');
          if (!gweMsgId) { await reply(interaction, token, 'Message ID is required.', true); break; }
          const gweKey = `${guildId}:${gweMsgId}`;
          const gwe = activeGiveaways.get(gweKey);
          if (!gwe) { await reply(interaction, token, '❌ No active giveaway with that message ID.', true); break; }
          activeGiveaways.delete(gweKey);
          await _endGiveaway(gweKey, gweMsgId, gwe);
          await reply(interaction, token, '✅ Giveaway ended!', true);
          break;
        }
        case 'giveaway-reroll': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const gwrMsgId = getOpt(interaction, 'message_id');
          if (!gwrMsgId) { await reply(interaction, token, 'Message ID is required.', true); break; }
          const gwrKey = `${guildId}:${gwrMsgId}`;
          const gwrEntries = giveawayEntries.get(gwrKey);
          if (!gwrEntries || !gwrEntries.size) { await reply(interaction, token, '❌ No entries found for that giveaway.', true); break; }
          const gwrChanId = getOpt(interaction, 'channel') || channelId;
          const gwrCount = Math.max(1, Math.min(20, parseInt(getOpt(interaction, 'winners') || '1', 10)));
          const gwrValid = [...gwrEntries].sort(() => Math.random() - 0.5).slice(0, gwrCount);
          const gwrWinnersText = gwrValid.map(id => `<@${id}>`).join(', ');
          await rest('POST', `/channels/${gwrChanId}/messages`, {
            embeds: [{
              title: '🎲 Giveaway Rerolled!',
              description: `New winner${gwrCount > 1 ? 's' : ''}: ${gwrWinnersText}\n\nCongratulations! 🎉`,
              color: 0x5865f2,
              footer: { text: `Rerolled from ${gwrEntries.size} entries` },
              timestamp: new Date().toISOString(),
            }]
          }, token).catch(() => {});
          await reply(interaction, token, `✅ Rerolled! New winner${gwrCount > 1 ? 's' : ''}: ${gwrWinnersText}`, true);
          break;
        }

        // ── Applications ──
        case 'apply': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const apTitle = getOpt(interaction, 'title') || 'Server Application';
          const apDesc = getOpt(interaction, 'description') || 'Fill out the form below to apply. Our staff team will review your application.';
          const apChanId = getOpt(interaction, 'channel') || channelId;
          const apStaffChanId = getOpt(interaction, 'staff_channel') || channelId;
          const apStaffRole = getOpt(interaction, 'staff_role') || null;
          const apColorRaw = (getOpt(interaction, 'color') || '#5865f2').replace('#', '');
          const apColor = parseInt(apColorRaw, 16) || 0x5865f2;
          const apImage = getOpt(interaction, 'image');
          const apQ1 = getOpt(interaction, 'question1') || 'Tell us about yourself.';
          const apQ2 = getOpt(interaction, 'question2');
          const apQ3 = getOpt(interaction, 'question3');
          const apQ4 = getOpt(interaction, 'question4');
          const questions = [apQ1, apQ2, apQ3, apQ4].filter(Boolean);
          const apConfigKey = `${guildId}_${Date.now()}`;
          applyConfigs.set(apConfigKey, { questions, staffChannelId: apStaffChanId, staffRoleId: apStaffRole, title: apTitle, guildId });
          const apEmbed = {
            title: apTitle,
            description: apDesc,
            color: isNaN(apColor) ? 0x5865f2 : apColor,
            footer: { text: 'Click the button below to start your application' },
            fields: questions.map((q, i) => ({ name: `Question ${i + 1}`, value: q, inline: false })),
            ...(apImage && /^https?:\/\//.test(apImage) ? { image: { url: apImage } } : {}),
          };
          const apMsgRes = await rest('POST', `/channels/${apChanId}/messages`, {
            embeds: [apEmbed],
            components: [{ type: 1, components: [{ type: 2, custom_id: `apply_now:${apConfigKey}`, label: 'Apply Now', style: 1, emoji: { name: '📋' } }] }]
          }, token);
          if (!apMsgRes.data?.id) { await reply(interaction, token, `Failed to post application form: ${apMsgRes.data?.message || 'Missing permissions'}`, true); break; }
          await reply(interaction, token, `✅ Application form posted in <#${apChanId}>!`, true);
          break;
        }

        // ── Role management ──
        case 'role-add': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const raTarget = getOpt(interaction, 'user');
          const raRole = getOpt(interaction, 'role');
          if (!raTarget || !raRole) { await reply(interaction, token, 'User and role are required.', true); break; }
          const raRes = await rest('PUT', `/guilds/${guildId}/members/${raTarget}/roles/${raRole}`, null, token);
          if (raRes.status < 200 || raRes.status >= 300) {
            await reply(interaction, token, `❌ Failed to add role: ${raRes.data?.message || 'Missing permissions or role is above bot\'s highest role'}`, true);
          } else {
            await replyEmbed(interaction, token, {
              title: '✅ Role Added',
              description: `<@&${raRole}> has been added to <@${raTarget}>.`,
              color: 0x57f287,
              footer: { text: `Added by ${caller.username || 'Moderator'}` },
              timestamp: new Date().toISOString(),
            });
          }
          break;
        }
        case 'role-remove': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const rrTarget = getOpt(interaction, 'user');
          const rrRole = getOpt(interaction, 'role');
          if (!rrTarget || !rrRole) { await reply(interaction, token, 'User and role are required.', true); break; }
          const rrRes = await rest('DELETE', `/guilds/${guildId}/members/${rrTarget}/roles/${rrRole}`, null, token);
          if (rrRes.status < 200 || rrRes.status >= 300) {
            await reply(interaction, token, `❌ Failed to remove role: ${rrRes.data?.message || 'Missing permissions or role is above bot\'s highest role'}`, true);
          } else {
            await replyEmbed(interaction, token, {
              title: '✅ Role Removed',
              description: `<@&${rrRole}> has been removed from <@${rrTarget}>.`,
              color: 0xed4245,
              footer: { text: `Removed by ${caller.username || 'Moderator'}` },
              timestamp: new Date().toISOString(),
            });
          }
          break;
        }

        // ── Sticky messages ──
        case 'sticky': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const stContent = getOpt(interaction, 'message') || '';
          const stTitle = getOpt(interaction, 'title');
          const stColorRaw = (getOpt(interaction, 'color') || '#5865f2').replace('#', '');
          const stColor = parseInt(stColorRaw, 16) || 0x5865f2;
          const stChanId = getOpt(interaction, 'channel') || channelId;
          if (!stContent && !stTitle) { await reply(interaction, token, 'Provide a message or title.', true); break; }
          stickyMessages.set(stChanId, { content: stContent, embedTitle: stTitle || null, color: isNaN(stColor) ? 0x5865f2 : stColor, guildId });
          // Delete old sticky pin if it exists
          const oldPin = stickyPinned.get(stChanId);
          if (oldPin) { await rest('DELETE', `/channels/${stChanId}/messages/${oldPin}`, null, token).catch(() => {}); stickyPinned.delete(stChanId); }
          // Post initial sticky
          const stPayload = stTitle
            ? { embeds: [{ title: stTitle, description: stContent || undefined, color: isNaN(stColor) ? 0x5865f2 : stColor, footer: { text: '📌 Sticky Message' } }] }
            : { content: `📌 **Sticky:** ${stContent}` };
          const stMsgRes = await rest('POST', `/channels/${stChanId}/messages`, stPayload, token);
          if (stMsgRes.data?.id) stickyPinned.set(stChanId, stMsgRes.data.id);
          await reply(interaction, token, `📌 Sticky message set in <#${stChanId}>!`, true);
          break;
        }
        case 'sticky-off': {
          if (!hasModPermission()) { await reply(interaction, token, MOD_DENIED, true); break; }
          const stOffChanId = getOpt(interaction, 'channel') || channelId;
          if (!stickyMessages.has(stOffChanId)) { await reply(interaction, token, '❌ No sticky message is set in that channel.', true); break; }
          stickyMessages.delete(stOffChanId);
          const oldPin = stickyPinned.get(stOffChanId);
          if (oldPin) { await rest('DELETE', `/channels/${stOffChanId}/messages/${oldPin}`, null, token).catch(() => {}); stickyPinned.delete(stOffChanId); }
          await reply(interaction, token, `✅ Sticky message removed from <#${stOffChanId}>.`, true);
          break;
        }

        default:
          await reply(interaction, token, `Command \`/${cmd}\` is not implemented yet.`, true);
      }
    } catch (e) {
      try { await reply(interaction, token, `Error: ${e.message}`, true); } catch {}
    }
  }

  // ── Gateway ──
  function send(payload) {
    if (ws && ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(payload));
  }

  // Exponential backoff: 1s, 2s, 4s, 8s, 16s, capped at 30s
  function _scheduleReconnect(delay) {
    if (dead || reconnectTimer) return;
    reconnectTimer = setTimeout(() => {
      reconnectTimer = null;
      _doConnect();
    }, delay != null ? delay : Math.min(1000 * Math.pow(2, _reconnectAttempts), 30000));
  }

  function _doConnect(forceIdentify) {
    if (dead) return;
    clearTimeout(reconnectTimer);
    reconnectTimer = null;
    // Null ws and strip listeners BEFORE terminating so its close event
    // doesn't see reconnectTimer===null and schedule a spurious second reconnect.
    if (ws) {
      const stale = ws;
      ws = null;
      stale.removeAllListeners();
      try { stale.terminate(); } catch {}
    }
    clearInterval(heartbeatInterval);
    heartbeatInterval = null;
    _heartbeatAcked = true;

    const gatewayUrl = (!forceIdentify && _resumeGatewayUrl)
      ? `${_resumeGatewayUrl}?v=10&encoding=json`
      : 'wss://gateway.discord.gg/?v=10&encoding=json';

    ws = new WebSocket(gatewayUrl);

    ws.on('open', () => { if (_onStatus) _onStatus({ online: false, status: 'Connecting...' }); });

    ws.on('message', (data) => {
      let msg;
      try { msg = JSON.parse(data); } catch { return; }
      const { op, d, s, t } = msg;
      if (s) lastSeq = s;

      if (op === 10) {
        const interval = d.heartbeat_interval;
        // Jitter on first heartbeat per Discord spec
        setTimeout(() => send({ op: 1, d: lastSeq }), Math.random() * interval);
        heartbeatInterval = setInterval(() => {
          if (!_heartbeatAcked) {
            // Zombie connection — gateway stopped ACKing; close and resume
            clearInterval(heartbeatInterval);
            heartbeatInterval = null;
            if (ws) { const stale = ws; ws = null; stale.removeAllListeners(); try { stale.terminate(); } catch {} }
            _scheduleReconnect(0);
            return;
          }
          _heartbeatAcked = false;
          send({ op: 1, d: lastSeq });
        }, interval);

        // Resume if we have a prior session; otherwise fresh IDENTIFY
        if (!forceIdentify && sessionId && lastSeq) {
          send({ op: 6, d: { token: _token, session_id: sessionId, seq: lastSeq } });
        } else {
          send({
            op: 2,
            d: {
              token: _token,
              intents: 1 | 2 | 128 | 512 | 1024 | 4096, // 4096 = DIRECT_MESSAGES (required for DM sext handler)
              properties: { os: 'windows', browser: 'kawaii', device: 'kawaii' },
              presence: { activities: [buildDefaultActivity()], status: 'online', afk: false }
            }
          });
        }
      } else if (op === 11) {
        // Heartbeat ACK
        _heartbeatAcked = true;
      } else if (op === 9) {
        // Invalid session — d=true means resumable, d=false means must re-identify
        const resumable = d === true;
        sessionId = resumable ? sessionId : null;
        lastSeq = resumable ? lastSeq : null;
        _reconnectAttempts++;
        _scheduleReconnect(resumable ? 2000 : 5000);
        return;
      } else if (op === 7) {
        // Server-requested reconnect — strip listeners before closing so close event doesn't double-schedule
        if (ws) { const stale = ws; ws = null; stale.removeAllListeners(); try { stale.close(1000); } catch {} }
        _scheduleReconnect(500);
        return;
      } else if (op === 0) {
        if (t === 'READY') {
          sessionId = d.session_id;
          botUser = d.user;
          _resumeGatewayUrl = d.resume_gateway_url || null;
          _reconnectAttempts = 0; // reset backoff on successful connect
          if (_onStatus) _onStatus({ online: true, status: 'Online', user: botUser });
          if (!_lyricOwner) startFunRotation();   // begin 60s rotating fun statuses
        } else if (t === 'GUILD_CREATE') {
          for (const vs of (d.voice_states || [])) {
            if (vs.user_id) memberVoiceStates.set(`${d.id}:${vs.user_id}`, vs.channel_id);
          }
        } else if (t === 'INTERACTION_CREATE' && d.type === 2) {
          handleCommand(d, _token).catch(() => {});
        } else if (t === 'INTERACTION_CREATE' && d.type === 3) {
          handleButton(d).catch(() => {});
        } else if (t === 'INTERACTION_CREATE' && d.type === 4) {
          handleAutocomplete(d, _token).catch(() => {});
        } else if (t === 'RESUMED') {
          _reconnectAttempts = 0; // session resumed successfully — reset backoff
          if (_onStatus) _onStatus({ online: true, status: 'Online', user: botUser });
        } else if (t === 'INTERACTION_CREATE' && d.type === 5) {
          handleModal(d).catch(() => {});
        } else if (t === 'GUILD_MEMBER_ADD') {
          // Autorole
          const arRoleId = guildAutoRole.get(d.guild_id);
          if (arRoleId) rest('PUT', `/guilds/${d.guild_id}/members/${d.user.id}/roles/${arRoleId}`, null, _token).catch(() => {});
          // Welcome embed
          const wc = guildWelcome.get(d.guild_id);
          if (wc) {
            (async () => {
              try {
                const gRes = await rest('GET', `/guilds/${d.guild_id}?with_counts=true`, null, _token);
                const gName = gRes.data?.name || 'this server';
                const gCount = gRes.data?.approximate_member_count ?? gRes.data?.member_count ?? '?';
                const avatarUrl = d.user.avatar
                  ? `https://cdn.discordapp.com/avatars/${d.user.id}/${d.user.avatar}.png`
                  : `https://cdn.discordapp.com/embed/avatars/${Number(BigInt(d.user.id) >> 22n) % 6}.png`;
                const desc = (wc.message || '')
                  .replace(/\{user\}/g, `<@${d.user.id}>`)
                  .replace(/\{username\}/g, d.user.global_name || d.user.username || 'someone')
                  .replace(/\{server\}/g, gName)
                  .replace(/\{count\}/g, String(gCount));
                const embed = {
                  title: wc.title || 'Welcome!',
                  description: desc,
                  color: wc.color ?? 0x5865f2,
                  timestamp: new Date().toISOString(),
                  footer: { text: wc.footer || `${gName} • Member #${gCount}` },
                };
                if (wc.thumbnail !== false) embed.thumbnail = { url: avatarUrl };
                if (wc.image) embed.image = { url: wc.image };
                rest('POST', `/channels/${wc.channelId}/messages`, { embeds: [embed] }, _token).catch(() => {});
              } catch {}
            })();
          }
        } else if (t === 'GUILD_MEMBER_REMOVE') {
          const gc = guildGoodbye.get(d.guild_id);
          if (gc) {
            (async () => {
              try {
                const gRes = await rest('GET', `/guilds/${d.guild_id}`, null, _token);
                const gName = gRes.data?.name || 'this server';
                const avatarUrl = d.user?.avatar
                  ? `https://cdn.discordapp.com/avatars/${d.user.id}/${d.user.avatar}.png`
                  : `https://cdn.discordapp.com/embed/avatars/0.png`;
                const desc = (gc.message || '')
                  .replace(/\{user\}/g, `<@${d.user?.id}>`)
                  .replace(/\{username\}/g, d.user?.global_name || d.user?.username || 'someone')
                  .replace(/\{server\}/g, gName);
                const embed = {
                  title: gc.title || 'Goodbye',
                  description: desc,
                  color: gc.color ?? 0xed4245,
                  timestamp: new Date().toISOString(),
                  footer: { text: gName },
                };
                if (gc.thumbnail !== false) embed.thumbnail = { url: avatarUrl };
                rest('POST', `/channels/${gc.channelId}/messages`, { embeds: [embed] }, _token).catch(() => {});
              } catch {}
            })();
          }
        } else if (t === 'MESSAGE_REACTION_ADD') {
          const rrKey = `${d.guild_id}:${d.message_id}`;
          const rrEntry = reactionRoles.get(rrKey);
          if (rrEntry && d.user_id !== botUser?.id) {
            const emoji = d.emoji?.id ? `${d.emoji.name}:${d.emoji.id}` : d.emoji?.name;
            const roleMap = rrEntry.roles || rrEntry;
            const rrRoleId = emoji && roleMap[emoji];
            if (rrRoleId) rest('PUT', `/guilds/${d.guild_id}/members/${d.user_id}/roles/${rrRoleId}`, null, _token).catch(() => {});
          }
          // Starboard
          if (d.emoji?.name === '⭐' && d.guild_id && d.user_id !== botUser?.id) {
            const sb = starboards.get(d.guild_id);
            if (sb && !sb.posted.has(d.message_id)) {
              (async () => {
                try {
                  const reacts = await rest('GET', `/channels/${d.channel_id}/messages/${d.message_id}/reactions/${encodeURIComponent('⭐')}?limit=100`, null, _token);
                  const count = Array.isArray(reacts.data) ? reacts.data.length : 1;
                  if (count >= sb.threshold) {
                    sb.posted.add(d.message_id);
                    const msgRes = await rest('GET', `/channels/${d.channel_id}/messages/${d.message_id}`, null, _token);
                    const m = msgRes.data;
                    const embed = {
                      description: (m.content || '').slice(0, 1000),
                      author: { name: m.author?.username || 'Unknown', icon_url: m.author?.avatar ? `https://cdn.discordapp.com/avatars/${m.author.id}/${m.author.avatar}.png` : undefined },
                      color: 0xfee75c,
                      footer: { text: `⭐ ${count} | in <#${d.channel_id}>` },
                      timestamp: m.timestamp
                    };
                    if (m.attachments?.[0]?.url) embed.image = { url: m.attachments[0].url };
                    rest('POST', `/channels/${sb.channelId}/messages`, { content: `https://discord.com/channels/${d.guild_id}/${d.channel_id}/${d.message_id}`, embeds: [embed] }, _token).catch(() => {});
                  }
                } catch {}
              })();
            }
          }
        } else if (t === 'MESSAGE_REACTION_REMOVE') {
          const rrKey = `${d.guild_id}:${d.message_id}`;
          const rrEntry = reactionRoles.get(rrKey);
          if (rrEntry && d.user_id !== botUser?.id) {
            const emoji = d.emoji?.id ? `${d.emoji.name}:${d.emoji.id}` : d.emoji?.name;
            const roleMap = rrEntry.roles || rrEntry;
            const rrRoleId = emoji && roleMap[emoji];
            if (rrRoleId) rest('DELETE', `/guilds/${d.guild_id}/members/${d.user_id}/roles/${rrRoleId}`, null, _token).catch(() => {});
          }
        } else if (t === 'MESSAGE_CREATE' && d.channel_id && d.author?.id !== botUser?.id) {
          // ── Shared sext visual sender — same girl each session via girlBase ──
          const _sendSextVisual = async (combinedText, girlBase, cfg, channelId, sentIds) => {
            const { q: vq } = pickSextVisualQuery(combinedText, girlBase);
            const post = await fetchRedgifsContent(vq, sentIds);
            if (post?.videoUrl || post?.url) {
              const postUrl = post.videoUrl || post.url;
              await rest('POST', `/channels/${channelId}/messages`, { content: postUrl }, _token).catch(() => {});
            }
          };

          // ── Shared sext sys-prompt builder ──
          const _sextSys = (cfg, location) => {
            const suffix = ` You are ${location}. Be raw, explicit, and passionate — 2-3 sentences max. Use sexy emojis like 💦😩🔥👅💋🤤😈😏🫦 naturally to feel like real sexting. ONLY append [SEND_VISUAL] at the end when the user explicitly asks to see you, requests a pic/photo/video/selfie/nudes/body/show me. ONLY append [SEND_ASMR] when they ask for moaning/audio/voice/whisper/wet sounds/make noise.`;
            return cfg.prompt ? `${cfg.prompt}${suffix}` : `You are ${cfg.name}, a ${cfg.persona.replace(/-/g, ' ')}. Style: ${cfg.style}.${suffix}`;
          };

          // ── Shared history compaction ──
          const _compactHistory = async (sess) => {
            if (sess.messages.length <= 20) return;
            const toSummarize = sess.messages.slice(0, 14);
            const fresh = sess.messages.slice(14);
            try {
              const sp = `Summarize this sexting conversation in 2 sentences. Be explicit and specific about what was discussed, requested, or promised:\n\n${toSummarize.map(m => `${m.role}: ${m.content}`).join('\n')}`;
              const summary = await groqSext([{ role: 'user', content: sp }], 'You are a concise summarizer. Respond with only the 2-sentence summary.');
              sess.messages = [{ role: 'system', content: `[Earlier: ${summary}]` }, ...fresh];
            } catch { sess.messages = sess.messages.slice(-10); }
          };

          // ── Sext DM handler ──
          if (!d.guild_id && sextHistory.has(d.author.id)) {
            (async () => {
              const sess = sextHistory.get(d.author.id);
              const cfg = sess.cfg || { name: 'Mia', persona: 'submissive-girlfriend', style: 'dirty' };
              const girlBase = sess.girlBase || cfg.girlBase || 'petite brunette amateur pov';
              const sysPrompt = _sextSys(cfg, 'sexting the user via Discord DM');
              // Detect image attachment (e.g. dick pic) — pass URL to vision model
              const imgAttachment = (d.attachments || []).find(a => a.content_type?.startsWith('image/'));
              const imageUrl = imgAttachment?.url || null;
              const userText = d.content || (imageUrl ? 'I just sent you a photo 😏' : '');
              sess.messages.push({ role: 'user', content: userText });
              await _compactHistory(sess);
              const wantsVisual = VISUAL_RE.test(userText);
              const wantsAsmr = ASMR_RE.test(userText);
              try {
                const aiReply = await groqSext(sess.messages, sysPrompt, imageUrl);
                const sendVisual = aiReply.includes('[SEND_VISUAL]');
                const sendAsmr = wantsAsmr || aiReply.includes('[SEND_ASMR]');
                const cleanReply = aiReply.replace(/\[SEND_VISUAL\]|\[SEND_ASMR\]/g, '').trim();
                sess.messages.push({ role: 'assistant', content: cleanReply });
                await rest('POST', `/channels/${d.channel_id}/messages`, { content: cleanReply }, _token);
                if (sendVisual) await _sendSextVisual(userText + ' ' + cleanReply, girlBase, cfg, d.channel_id, sess.sentIds);
                if (sendAsmr) {
                  const asmrBuf = await fetchAsmrClip(cfg.persona.replace(/-/g, ' '), detectAsmrType(userText));
                  if (asmrBuf) await restMultipart('POST', `/channels/${d.channel_id}/messages`, {}, [{ name: 'voice.mp3', mime: 'audio/mpeg', data: asmrBuf }], _token).catch(() => {});
                }
              } catch {}
            })();
          } else if (d.guild_id && d.mentions?.some(m => m.id === botUser?.id)) {
            // ── Sext channel handler — @ mention in a guild channel ──
            if (!nsfwChannels.has(d.channel_id)) {
              rest('POST', `/channels/${d.channel_id}/messages`, { content: '🔞 This is not an NSFW channel. Please use the designated NSFW channel to chat with me.' }, _token).catch(() => {});
            } else {
              (async () => {
                const sessKey = `${d.guild_id}:${d.author.id}`;
                const cfg = sextConfig.get(d.guild_id) || { name: 'Mia', persona: 'submissive-girlfriend', style: 'dirty', girlBase: 'petite brunette amateur pov' };
                if (!sextChannelSessions.has(sessKey)) {
                  sextChannelSessions.set(sessKey, { messages: [], channelId: d.channel_id, cfg, sentIds: new Set(), girlBase: cfg.girlBase || 'petite brunette amateur pov' });
                }
                const sess = sextChannelSessions.get(sessKey);
                const girlBase = sess.girlBase || cfg.girlBase || 'petite brunette amateur pov';
                const sysPrompt = _sextSys(cfg, 'chatting with the user in a Discord server NSFW channel');
                const imgAttachment = (d.attachments || []).find(a => a.content_type?.startsWith('image/'));
                const imageUrl = imgAttachment?.url || null;
                const userMsg = (d.content.replace(/<@!?\d+>/g, '').trim()) || (imageUrl ? 'I just sent you a photo 😏' : '');
                if (!userMsg && !imageUrl) return;
                sess.messages.push({ role: 'user', content: userMsg });
                await _compactHistory(sess);
                const wantsAsmr = ASMR_RE.test(userMsg);
                try {
                  const aiReply = await groqSext(sess.messages, sysPrompt, imageUrl);
                  const sendVisual = aiReply.includes('[SEND_VISUAL]');
                  const sendAsmr = wantsAsmr || aiReply.includes('[SEND_ASMR]');
                  const cleanReply = aiReply.replace(/\[SEND_VISUAL\]|\[SEND_ASMR\]/g, '').trim();
                  sess.messages.push({ role: 'assistant', content: cleanReply });
                  await rest('POST', `/channels/${d.channel_id}/messages`, { content: `<@${d.author.id}> ${cleanReply}` }, _token);
                  if (sendVisual) await _sendSextVisual(userMsg + ' ' + cleanReply, girlBase, cfg, d.channel_id, sess.sentIds);
                  if (sendAsmr) {
                    const asmrBuf = await fetchAsmrClip(cfg.persona.replace(/-/g, ' '), detectAsmrType(userMsg));
                    if (asmrBuf) await restMultipart('POST', `/channels/${d.channel_id}/messages`, {}, [{ name: 'voice.mp3', mime: 'audio/mpeg', data: asmrBuf }], _token).catch(() => {});
                  }
                } catch {}
              })();
            }
          }
          // Trivia answer check
          const trivSess = triviaSessions.get(d.channel_id);
          if (trivSess && /^[1-4]$/.test((d.content || '').trim())) {
            if (Date.now() > trivSess.expiresAt) {
              triviaSessions.delete(d.channel_id);
            } else {
              triviaSessions.delete(d.channel_id);
              const guess = parseInt(d.content.trim(), 10);
              const correct = guess === trivSess.correctIndex;
              const NUM_EMOJIS = ['1️⃣','2️⃣','3️⃣','4️⃣'];
              rest('POST', `/channels/${d.channel_id}/messages`, {
                embeds: [{
                  title: correct ? '✅ Correct!' : '❌ Wrong!',
                  description: correct
                    ? `<@${d.author.id}> answered ${NUM_EMOJIS[guess - 1]} **${guess}** — that's right! 🎉`
                    : `<@${d.author.id}> answered ${NUM_EMOJIS[guess - 1]} **${guess}** — not quite!\n\n✅ The correct answer was **${trivSess.correctIndex}. ${trivSess.correctAnswer}**`,
                  color: correct ? 0x57f287 : 0xed4245,
                  footer: { text: trivSess.category },
                }],
              }, _token).catch(() => {});
            }
          }
          // Auto-delete
          const adSecs = autoDelete.get(d.channel_id);
          if (adSecs && adSecs > 0 && d.id) {
            setTimeout(() => rest('DELETE', `/channels/${d.channel_id}/messages/${d.id}`, null, _token).catch(() => {}), adSecs * 1000);
          }
          // Sticky messages — delete old pin and repost at bottom
          const stCfg = stickyMessages.get(d.channel_id);
          if (stCfg && d.author?.id !== botUser?.id) {
            (async () => {
              const oldPin = stickyPinned.get(d.channel_id);
              if (oldPin) {
                await rest('DELETE', `/channels/${d.channel_id}/messages/${oldPin}`, null, _token).catch(() => {});
                stickyPinned.delete(d.channel_id);
              }
              const stPayload = stCfg.embedTitle
                ? { embeds: [{ title: stCfg.embedTitle, description: stCfg.content || undefined, color: stCfg.color, footer: { text: '📌 Sticky Message' } }] }
                : { content: `📌 **Sticky:** ${stCfg.content}` };
              const newMsg = await rest('POST', `/channels/${d.channel_id}/messages`, stPayload, _token).catch(() => null);
              if (newMsg?.data?.id) stickyPinned.set(d.channel_id, newMsg.data.id);
            })();
          }
        } else if (t === 'VOICE_STATE_UPDATE') {
          if (d.guild_id && d.user_id) {
            memberVoiceStates.set(`${d.guild_id}:${d.user_id}`, d.channel_id);
            // If the bot itself was removed from a VC, clean up all voice state for that guild
            if (d.user_id === botUser?.id && !d.channel_id) {
              _dtStop(d.guild_id);
              stop(d.guild_id);
            }
          }
          const pv = pendingVoice.get(d.guild_id);
          if (pv) pv.vsu(d);
          const adapter = voiceAdapters.get(d.guild_id);
          if (adapter) adapter.onVoiceStateUpdate(d);
        } else if (t === 'VOICE_SERVER_UPDATE') {
          const pv = pendingVoice.get(d.guild_id);
          if (pv) pv.vsru(d);
          const adapter = voiceAdapters.get(d.guild_id);
          if (adapter) adapter.onVoiceServerUpdate(d);
        }
      }
    });

    ws.on('close', (code) => {
      clearInterval(heartbeatInterval);
      // Fatal codes — do not reconnect (bad token, invalid intents, disallowed intents, etc.)
      const FATAL = [4004, 4010, 4011, 4012, 4013, 4014];
      if (dead || FATAL.includes(code)) {
        if (code === 4004) { if (_onStatus) _onStatus({ online: false, status: 'Invalid token' }); }
        return;
      }
      if (_onStatus) _onStatus({ online: false, status: 'Reconnecting...' });
      _reconnectAttempts++;
      // Non-resumable close codes — must re-identify
      const NO_RESUME = [4007, 4009];
      if (NO_RESUME.includes(code)) { sessionId = null; lastSeq = null; }
      _scheduleReconnect();
    });

    ws.on('error', () => { if (_onStatus) _onStatus({ online: false, status: 'Connection error' }); });
  }

  function connect(token, onStatus) {
    _token = token;
    _onStatus = onStatus;
    dead = false;
    startTime = Date.now();
    _reconnectAttempts = 0;
    sessionId = null;
    lastSeq = null;
    _resumeGatewayUrl = null;
    _doConnect(true); // always fresh IDENTIFY on first connect
  }

  function _genCaptcha(type) {
    const r = (a, b) => Math.floor(Math.random() * (b - a + 1)) + a;
    if (type === 'math') {
      const ops = ['+', '-', '*'];
      const op = ops[r(0, 2)];
      let a, b, answer;
      if (op === '+') { a = r(3, 25); b = r(3, 25); answer = a + b; }
      else if (op === '-') { a = r(15, 40); b = r(1, a - 1); answer = a - b; }
      else { a = r(2, 9); b = r(2, 9); answer = a * b; }
      return { question: `Solve: ${a} ${op} ${b} = ?`, answer: String(answer), placeholder: 'Type the number answer…' };
    }
    if (type === 'text') {
      const words = ['DISCORD','SERVER','MEMBER','VERIFY','ACCESS','GAMING','ONLINE','ACTIVE','SECURE','PORTAL','UNLOCK','JOINED'];
      const word = words[r(0, words.length - 1)];
      return { question: `Type this word exactly: ${word}`, answer: word.toLowerCase(), placeholder: 'Type the word (case does not matter)…' };
    }
    if (type === 'number') {
      const n = r(1000, 9999);
      return { question: `Type this number exactly: ${n}`, answer: String(n), placeholder: 'Type the 4-digit number…' };
    }
    return null;
  }

  async function _endGiveaway(gwKey, msgId, gw) {
    const entries = giveawayEntries.get(gwKey);
    const valid = entries ? [...entries] : [];
    let winnersText, winnerIds = [];
    if (!valid.length) {
      winnersText = '*No entries received — no winner this time.*';
    } else {
      const shuffled = valid.sort(() => Math.random() - 0.5);
      winnerIds = shuffled.slice(0, Math.min(gw.winnerCount, shuffled.length));
      winnersText = winnerIds.map(id => `<@${id}>`).join(', ');
      await rest('POST', `/channels/${gw.channelId}/messages`, {
        content: `🎉 Congratulations ${winnersText}! You won **${gw.prize}**!\n> Jump to giveaway: https://discord.com/channels/${gw.guildId}/${gw.channelId}/${msgId}`
      }, _token).catch(() => {});
    }
    const endEmbed = {
      title: '🎊 Giveaway Ended!',
      description: [`**Prize:** ${gw.prize}`, '', `**Winner${gw.winnerCount > 1 ? 's' : ''}:** ${winnersText}`, '', '*Use `/giveaway-reroll` to pick new winners.*'].join('\n'),
      color: 0x57f287,
      footer: { text: `${valid.length} entr${valid.length === 1 ? 'y' : 'ies'} • Ended` },
      timestamp: new Date().toISOString(),
    };
    await rest('PATCH', `/channels/${gw.channelId}/messages/${msgId}`, {
      embeds: [endEmbed],
      components: [{ type: 1, components: [{ type: 2, custom_id: 'giveaway_enter', label: 'Giveaway Ended', style: 2, emoji: { name: '🎊' }, disabled: true }] }]
    }, _token).catch(() => {});
  }

  async function handleButton(d) {
    const customId = d.data?.custom_id || '';
    const ackEphemeral = (content) => rest('POST', `/interactions/${d.id}/${d.token}/callback`,
      { type: 4, data: { content, flags: 64 } }, _token);
    const ackEmbed = (embed) => rest('POST', `/interactions/${d.id}/${d.token}/callback`,
      { type: 4, data: { embeds: [embed], flags: 64 } }, _token);

    // ── Now-playing player buttons ──
    if (customId.startsWith('np_')) {
      // guildId is always the last underscore-segment (pure numeric Discord snowflake)
      const lastUnd = customId.lastIndexOf('_');
      const npGuildId = customId.slice(lastUnd + 1);
      const action    = customId.slice('np_'.length, lastUnd); // e.g. 'loop', 'filter_bass', 'setdj'

      const refreshNp = () => {
        const np = nowPlayingMsgs.get(npGuildId);
        if (np) return updateNowPlaying(npGuildId, np.track).catch(() => {});
      };

      if (action === 'stop') {
        stop(npGuildId);
        const np = nowPlayingMsgs.get(npGuildId);
        if (np) { nowPlayingMsgs.delete(npGuildId); try { await rest('DELETE', `/channels/${np.channelId}/messages/${np.messageId}`, null, _token); } catch {} }
        await ackEphemeral('⏹ Stopped.');

      } else if (action === 'skip') {
        skip(npGuildId);
        await ackEphemeral('⏭ Skipped.');

      } else if (action === 'pause') {
        pause(npGuildId);
        await ackEphemeral('⏸ Paused.');

      } else if (action === 'resume') {
        resume(npGuildId);
        await ackEphemeral('▶ Resumed.');

      } else if (action === 'rewind') {
        const ok = await rewind(npGuildId);
        await ackEphemeral(ok ? '⏮ Rewound to start.' : 'Nothing to rewind.');

      } else if (action === 'shuffle') {
        shuffleQueue(npGuildId);
        await ackEphemeral('🔀 Queue shuffled.');

      } else if (action === 'loop') {
        const looping = toggleLoop(npGuildId);
        await refreshNp();
        await ackEphemeral(looping ? '🔂 Loop enabled.' : '🔂 Loop disabled.');

      } else if (action === 'loopall') {
        const la = toggleLoopAll(npGuildId);
        await refreshNp();
        await ackEphemeral(la ? '🔁 Loop All enabled.' : '🔁 Loop All disabled.');

      } else if (action === 'queue') {
        const state = getMusicState(npGuildId);
        if (!state.queue.length) {
          await ackEphemeral('📋 The queue is empty.');
        } else {
          const lines = state.queue.slice(0, 15).map((t, i) =>
            `${i + 1}. **${t.name || t.title || 'Unknown'}**${t.artist ? ` — ${t.artist}` : ''}`);
          if (state.queue.length > 15) lines.push(`*… and ${state.queue.length - 15} more*`);
          await ackEphemeral(`📋 **Queue — ${state.queue.length} track${state.queue.length > 1 ? 's' : ''}**\n${lines.join('\n')}`);
        }

      } else if (action === 'add') {
        await rest('POST', `/interactions/${d.id}/${d.token}/callback`, {
          type: 9,
          data: {
            title: 'Add Song to Queue',
            custom_id: `np_modal_${npGuildId}`,
            components: [{ type: 1, components: [{ type: 4, custom_id: 'np_song_query', label: 'Song name or YouTube URL', style: 1, placeholder: 'e.g. Drake Gods Plan', required: true }] }]
          }
        }, _token);

      } else if (action === 'filters') {
        // Show ephemeral filter panel with toggle buttons
        await rest('POST', `/interactions/${d.id}/${d.token}/callback`, {
          type: 4,
          data: { flags: 64, content: '🎛️ **Audio Filters** — click to toggle:', components: [_filterComponents(npGuildId)] }
        }, _token);

      } else if (['filter_bass','filter_chipmunk','filter_vapor','filter_8d','filter_reverb','filter_earrape','filter_slowed'].includes(action)) {
        const state = getMusicState(npGuildId);
        if (!state.filters) state.filters = {};
        if (action === 'filter_bass') {
          state.filters.bassboost = state.filters.bassboost ? false : 'medium';
        } else if (action === 'filter_chipmunk') {
          state.filters.chipmunk = !state.filters.chipmunk;
          if (state.filters.chipmunk) state.filters.vaporwave = state.filters.slowed = false;
        } else if (action === 'filter_vapor') {
          state.filters.vaporwave = !state.filters.vaporwave;
          if (state.filters.vaporwave) state.filters.chipmunk = state.filters.slowed = false;
        } else if (action === 'filter_slowed') {
          state.filters.slowed = !state.filters.slowed;
          if (state.filters.slowed) state.filters.chipmunk = state.filters.vaporwave = false;
        } else if (action === 'filter_8d') {
          state.filters['8d'] = !state.filters['8d'];
        } else if (action === 'filter_reverb') {
          state.filters.reverb = !state.filters.reverb;
        } else if (action === 'filter_earrape') {
          state.filters.earrape = !state.filters.earrape;
        }
        // Seek to current position so filter applies without restarting from the top
        if (state.nowPlaying) {
          state.seekSeconds = _getPlaybackPos(state);
          state.queue.unshift(state.nowPlaying);
          state.nowPlaying = null;
          state.trackStartedAt = null;
          state.pausedAt = null;
          if (state.player) state.player.stop();
        }
        // Update the ephemeral filter panel in-place (type 7 = UPDATE_MESSAGE)
        await rest('POST', `/interactions/${d.id}/${d.token}/callback`, {
          type: 7, data: { content: '🎛️ **Audio Filters** — click to toggle:', components: [_filterComponents(npGuildId)] }
        }, _token);
        refreshNp();

      } else if (action === 'lock') {
        const state = getMusicState(npGuildId);
        state.locked = !state.locked;
        await refreshNp();
        await ackEphemeral(state.locked
          ? '🔒 Queue locked — only DJ role holders and admins can add songs.'
          : '🔓 Queue unlocked.');

      } else if (action === 'setdj') {
        await rest('POST', `/interactions/${d.id}/${d.token}/callback`, {
          type: 9,
          data: {
            title: 'Set DJ Role',
            custom_id: `np_setdj_modal_${npGuildId}`,
            components: [{ type: 1, components: [{ type: 4, custom_id: 'np_dj_role_name', label: 'Role name (e.g. DJ, Music, VIP)', style: 1, placeholder: 'Type exact role name…', required: true, max_length: 100 }] }]
          }
        }, _token);

      } else if (action === 'voldown' || action === 'volup') {
        const state = getMusicState(npGuildId);
        const delta = action === 'volup' ? 0.1 : -0.1;
        const newVol = Math.max(0, Math.min(1.5, (state.volume || 0.5) + delta));
        state.volume = newVol;
        setVcVolume(npGuildId, newVol);
        const pct = Math.round(newVol * 100);
        await refreshNp();
        await ackEphemeral(`🔊 Volume: **${pct}%**`);
      }
      return;
    }

    const guildId = d.guild_id;
    const userId = d.member?.user?.id || d.user?.id;
    const channelId = d.channel_id;

    try {
      const grantRoleByRegex = async (regex) => {
        const rolesRes = await rest('GET', `/guilds/${guildId}/roles`, null, _token);
        const roles = Array.isArray(rolesRes.data) ? rolesRes.data : [];
        const role = roles.find(r => r.name !== '@everyone' && regex.test(r.name));
        if (!role) return { ok: false, reason: 'no-role' };
        const memberData = await rest('GET', `/guilds/${guildId}/members/${userId}`, null, _token);
        const has = Array.isArray(memberData.data?.roles) && memberData.data.roles.includes(role.id);
        if (has) return { ok: true, role, already: true };
        const r = await rest('PUT', `/guilds/${guildId}/members/${userId}/roles/${role.id}`, null, _token);
        return { ok: r.status < 300, role, message: r.data?.message };
      };

      const openTicket = async (kind, intro) => {
        const channelsRes = await rest('GET', `/guilds/${guildId}/channels`, null, _token);
        const chs = Array.isArray(channelsRes.data) ? channelsRes.data : [];
        const cat = chs.find(c => c.type === 4 && /ticket/i.test(c.name));
        const uname = (d.member?.user?.username || 'user').toLowerCase().replace(/[^a-z0-9]/g, '').slice(0, 20) || 'user';
        const chanName = `${kind}-${uname}-${Date.now().toString().slice(-4)}`;
        const VIEW = 1 << 10, SEND = 1 << 11, HIST = 1 << 16;
        const allowBits = String(VIEW | SEND | HIST);
        const create = await rest('POST', `/guilds/${guildId}/channels`, {
          name: chanName,
          type: 0,
          parent_id: cat?.id,
          permission_overwrites: [
            { id: guildId, type: 0, deny: String(VIEW) },
            { id: userId,  type: 1, allow: allowBits }
          ]
        }, _token);
        if (create.status >= 200 && create.status < 300 && create.data?.id) {
          const ch = create.data;
          await rest('POST', `/channels/${ch.id}/messages`, {
            content: intro || `<@${userId}> Welcome! Staff will be with you shortly. Use the button below to close this ticket.`,
            components: [{ type: 1, components: [{ type: 2, style: 4, label: 'Close Ticket', custom_id: 'ticket_close' }] }]
          }, _token);
          await ackEphemeral(`Ticket created: <#${ch.id}>`);
          return ch;
        }
        await ackEphemeral(`Could not create ticket: ${create.data?.message || 'permission error'}`);
        return null;
      };

      // ── Role toggle: role_<name> or role:<roleId> ──
      if (customId.startsWith('role_') || customId.startsWith('role:')) {
        let roleId = null;
        let label = '';
        if (customId.startsWith('role:')) {
          roleId = customId.slice(5);
        } else {
          label = customId.slice(5).replace(/_/g, ' ');
          const rolesRes = await rest('GET', `/guilds/${guildId}/roles`, null, _token);
          if (rolesRes.status === 200 && Array.isArray(rolesRes.data)) {
            const norm = s => s.toLowerCase().replace(/[^a-z0-9]/g, '');
            const target = norm(label);
            const match = rolesRes.data.find(r => norm(r.name) === target);
            if (match) roleId = match.id;
          }
        }
        if (!roleId) {
          await ackEphemeral(`No role matching \`${label || customId}\` found. Create it first.`);
          return;
        }
        const memberRes = await rest('GET', `/guilds/${guildId}/members/${userId}`, null, _token);
        const hasRole = Array.isArray(memberRes.data?.roles) && memberRes.data.roles.includes(roleId);
        if (hasRole) {
          const r = await rest('DELETE', `/guilds/${guildId}/members/${userId}/roles/${roleId}`, null, _token);
          await ackEphemeral(r.status < 300 ? `Removed <@&${roleId}> from you.` : `Could not remove role: ${r.data?.message || 'permission error'}`);
        } else {
          const r = await rest('PUT', `/guilds/${guildId}/members/${userId}/roles/${roleId}`, null, _token);
          await ackEphemeral(r.status < 300 ? `Gave you <@&${roleId}>.` : `Could not add role: ${r.data?.message || 'permission error'}`);
        }
        return;
      }

      // ── Rules accept: grant Member/Verified role if present ──
      if (customId === 'rules_accept') {
        const rolesRes = await rest('GET', `/guilds/${guildId}/roles`, null, _token);
        const pick = Array.isArray(rolesRes.data) && rolesRes.data.find(r => /^(member|verified|accepted)$/i.test(r.name));
        if (pick) {
          const r = await rest('PUT', `/guilds/${guildId}/members/${userId}/roles/${pick.id}`, null, _token);
          await ackEphemeral(r.status < 300 ? `Thanks for accepting the rules! You now have <@&${pick.id}>.` : `Thanks for accepting the rules! (Could not assign role: ${r.data?.message || 'permission error'})`);
        } else {
          await ackEphemeral('Thanks for accepting the rules!');
        }
        return;
      }

      // ── Ticket create ──
      if (customId === 'ticket_create') {
        await openTicket('ticket');
        return;
      }

      if (customId === 'ticket_close') {
        await rest('POST', `/interactions/${d.id}/${d.token}/callback`,
          { type: 4, data: { content: 'Closing ticket in 5 seconds...' } }, _token);
        setTimeout(async () => { try { await rest('DELETE', `/channels/${channelId}`, null, _token); } catch {} }, 5000);
        return;
      }

      if (customId === 'ticket_faq') {
        await ackEmbed({
          title: 'Ticket FAQ',
          description: '**When will I get a response?** Staff typically reply within a few hours.\n**What info should I provide?** Describe your issue clearly and include screenshots if relevant.\n**Can I close my own ticket?** Yes — use the Close Ticket button inside your ticket channel.',
          color: 0x5865f2
        });
        return;
      }

      // ── Application button ──
      if (customId.startsWith('apply_now:')) {
        const apCfgKey = customId.slice('apply_now:'.length);
        const apCfg = applyConfigs.get(apCfgKey);
        if (!apCfg) { await ackEphemeral('❌ This application form is no longer active.'); return; }
        const modalComponents = apCfg.questions.slice(0, 4).map((q, i) => ({
          type: 1,
          components: [{ type: 4, custom_id: `apply_q${i}`, label: q.slice(0, 45), style: 2, placeholder: 'Type your answer here...', min_length: 1, max_length: 1000, required: true }]
        }));
        await rest('POST', `/interactions/${d.id}/${d.token}/callback`, {
          type: 9,
          data: { title: apCfg.title.slice(0, 45), custom_id: `apply_modal:${apCfgKey}`, components: modalComponents }
        }, _token);
        return;
      }

      // ── Giveaway entry ──
      if (customId === 'giveaway_enter') {
        const key = `${guildId}:${d.message?.id}`;
        // Check if giveaway is still active
        if (!activeGiveaways.has(key)) { await ackEphemeral('❌ This giveaway has already ended.'); return; }
        const gw = activeGiveaways.get(key);
        // Check required role
        if (gw.requiredRole) {
          const memRes = await rest('GET', `/guilds/${guildId}/members/${userId}`, null, _token).catch(() => ({ data: {} }));
          const memberRoles = Array.isArray(memRes.data?.roles) ? memRes.data.roles : [];
          if (!memberRoles.includes(gw.requiredRole)) {
            await ackEphemeral(`❌ You need the <@&${gw.requiredRole}> role to enter this giveaway.`);
            return;
          }
        }
        if (!giveawayEntries.has(key)) giveawayEntries.set(key, new Set());
        const set = giveawayEntries.get(key);
        if (set.has(userId)) {
          await ackEphemeral(`✅ You're already entered! Total entries: **${set.size}**`);
        } else {
          set.add(userId);
          await ackEphemeral(`🎉 You're entered! Total entries: **${set.size}**`);
        }
        return;
      }

      // ── Verify button — opens captcha modal or sends plain welcome ──
      if (customId.startsWith('welcome_verify:') || customId === 'welcome_verify' || customId === 'get_started') {
        const captchaType = customId.includes(':') ? customId.split(':')[1] : 'none';
        if (captchaType !== 'none') {
          const cap = _genCaptcha(captchaType);
          if (cap) {
            await rest('POST', `/interactions/${d.id}/${d.token}/callback`, {
              type: 9,
              data: {
                custom_id: `captcha_v:${cap.answer}`,
                title: '🔐 Server Verification',
                components: [{ type: 1, components: [{
                  type: 4, custom_id: 'captcha_input',
                  label: cap.question,
                  style: 1,
                  placeholder: cap.placeholder,
                  min_length: 1, max_length: 32,
                  required: true
                }]}]
              }
            }, _token);
            return;
          }
        }
        // No captcha — grant Member/Verified role then confirm access
        let verifyGranted = '';
        try {
          const rolesRes = await rest('GET', `/guilds/${guildId}/roles`, null, _token);
          const roles = Array.isArray(rolesRes.data) ? rolesRes.data : [];
          const target = roles.find(r => /^(member|verified|accepted|joined|welcomed?)$/i.test(r.name));
          if (target) {
            const memberRes = await rest('GET', `/guilds/${guildId}/members/${userId}`, null, _token);
            const hasIt = Array.isArray(memberRes.data?.roles) && memberRes.data.roles.includes(target.id);
            if (!hasIt) {
              await rest('PUT', `/guilds/${guildId}/members/${userId}/roles/${target.id}`, null, _token);
              verifyGranted = ` You've been given <@&${target.id}> — you now have full access to the server.`;
            } else {
              verifyGranted = ` You already have <@&${target.id}>.`;
            }
          }
        } catch (e) { /* still welcome them even if role grant fails */ }
        await ackEphemeral(`Welcome to the server, <@${userId}>! 🎉${verifyGranted} Head to the roles channel to pick your roles.`);
        return;
      }

      // ── Announcement subscribe: toggle an announcement-pings role ──
      if (customId === 'announcement_sub') {
        const rolesRes = await rest('GET', `/guilds/${guildId}/roles`, null, _token);
        const roles = Array.isArray(rolesRes.data) ? rolesRes.data : [];
        const role = roles.find(r => r.name !== '@everyone' && /^(announcements?|announce|notifications?|notify|news|pings?|updates?)$/i.test(r.name));
        if (!role) {
          await ackEphemeral('No announcements role found. Ask an admin to create a role named "Announcements" or "Notifications".');
          return;
        }
        const memberData = await rest('GET', `/guilds/${guildId}/members/${userId}`, null, _token);
        const has = Array.isArray(memberData.data?.roles) && memberData.data.roles.includes(role.id);
        if (has) {
          const r = await rest('DELETE', `/guilds/${guildId}/members/${userId}/roles/${role.id}`, null, _token);
          await ackEphemeral(r.status < 300 ? `Unsubscribed. Removed <@&${role.id}>.` : `Could not remove role: ${r.data?.message || 'permission error'}`);
        } else {
          const r = await rest('PUT', `/guilds/${guildId}/members/${userId}/roles/${role.id}`, null, _token);
          await ackEphemeral(r.status < 300 ? `Subscribed! You will be pinged via <@&${role.id}> for announcements.` : `Could not assign role: ${r.data?.message || 'permission error'}`);
        }
        return;
      }

      // ── FAQ "Contact Support" → open support ticket ──
      if (customId === 'faq_support') {
        await openTicket('support', `<@${userId}> Support ticket opened. Describe your issue in detail and a staff member will help you shortly.`);
        return;
      }

      // ── Changelog "Report Bug" → open bug-report ticket ──
      if (customId === 'changelog_bug') {
        await openTicket('bug', `<@${userId}> Bug report opened. Please include:\n- What you expected to happen\n- What actually happened\n- Steps to reproduce\n\nStaff will follow up here.`);
        return;
      }

      // ── NSFW age gate button ──
      if (customId.startsWith('nsfw_age_gate:')) {
        const ageRoleId = customId.split(':')[1];
        if (ageRoleId && guildId && userId) {
          const r = await rest('PUT', `/guilds/${guildId}/members/${userId}/roles/${ageRoleId}`, null, _token);
          if (r.status < 300) await ackEphemeral('✅ Verified! You now have access to NSFW channels.');
          else await ackEphemeral(`❌ Could not assign role — contact an admin. (${r.data?.message || 'permission error'})`);
        }
        return;
      }

      // ── Help pagination buttons ──
      if (customId.startsWith('help_prev:') || customId.startsWith('help_next:')) {
        const sessionId = customId.split(':').slice(1).join(':');
        const session = helpSessions.get(sessionId);
        if (!session) {
          await rest('POST', `/interactions/${d.id}/${d.token}/callback`,
            { type: 6 }, _token); // ack
          return;
        }
        if (session.userId !== userId) {
          await rest('POST', `/interactions/${d.id}/${d.token}/callback`,
            { type: 4, data: { content: 'Only the person who ran /help can navigate these pages.', flags: 64 } }, _token);
          return;
        }
        if (customId.startsWith('help_prev:')) session.page = Math.max(0, session.page - 1);
        else session.page = Math.min(session.pages.length - 1, session.page + 1);
        const pg = session.pages[session.page];
        const embed = {
          title: pg.title,
          description: pg.description,
          color: pg.color,
          footer: { text: pg.footer.text.replace('{page}', session.page + 1).replace('{total}', session.pages.length) }
        };
        const components = [{
          type: 1,
          components: [
            { type: 2, style: 2, label: '◀ Previous', custom_id: `help_prev:${sessionId}`, disabled: session.page === 0 },
            { type: 2, style: 2, label: 'Next ▶', custom_id: `help_next:${sessionId}`, disabled: session.page === session.pages.length - 1 }
          ]
        }];
        await rest('POST', `/interactions/${d.id}/${d.token}/callback`,
          { type: 7, data: { embeds: [embed], components } }, _token);
        return;
      }

      // ── Music control buttons (from /play response) ──
      if (customId.startsWith('music_pause:') || customId.startsWith('music_skip:') || customId.startsWith('music_stop:') || customId.startsWith('music_resume:')) {
        const colonIdx = customId.indexOf(':');
        const action = customId.slice(0, colonIdx);
        const targetGuildId = customId.slice(colonIdx + 1);
        if (action === 'music_pause') {
          const state = getMusicState(targetGuildId);
          if (state.paused) { resume(targetGuildId); await rest('POST', `/interactions/${d.id}/${d.token}/callback`, { type: 4, data: { content: '▶ Resumed.', flags: 64 } }, _token); }
          else { pause(targetGuildId); await rest('POST', `/interactions/${d.id}/${d.token}/callback`, { type: 4, data: { content: '⏸ Paused.', flags: 64 } }, _token); }
        } else if (action === 'music_skip') {
          skip(targetGuildId);
          await rest('POST', `/interactions/${d.id}/${d.token}/callback`, { type: 4, data: { content: '⏭ Skipped.', flags: 64 } }, _token);
        } else if (action === 'music_stop') {
          stop(targetGuildId);
          await rest('POST', `/interactions/${d.id}/${d.token}/callback`, { type: 4, data: { content: '⏹ Stopped.', flags: 64 } }, _token);
        } else if (action === 'music_resume') {
          resume(targetGuildId);
          await rest('POST', `/interactions/${d.id}/${d.token}/callback`, { type: 4, data: { content: '▶ Resumed.', flags: 64 } }, _token);
        }
        return;
      }

      // ── Dirty Talk next button ──
      if (customId.startsWith('dt_next:')) {
        const targetGuildId = customId.slice('dt_next:'.length);
        const dt = dtState.get(targetGuildId);
        if (!dt) { await ackEphemeral('Session ended. Use /dirtytalk to start a new one.'); return; }
        const userId = d.member?.user?.id || d.user?.id;
        const userVcId = memberVoiceStates.get(`${targetGuildId}:${userId}`);
        if (!userVcId) { await ackEphemeral('🎧 Join a voice channel first.'); return; }
        // Defer the update so the button shows a loading state while we search
        await rest('POST', `/interactions/${d.id}/${d.token}/callback`, { type: 6 }, _token);
        const { dtType: nType } = dt;
        const DT_NEXT_LABELS = { dirtytalk:'💬 Dirty Talk', moaning:'😩 Moaning & Orgasm', wetpussy:'💦 Wet Pussy ASMR', blowjob:'👅 Blowjob Sounds', fucking:'🔥 Fucking Sounds', whisper:'🎧 Whisper Roleplay', milf:'🍷 Mature / MILF', joi:'😈 JOI', femdom:'👠 Femdom / Dominant', young:'🌸 Young Girlfriend' };
        const GWA_NEXT = { dirtytalk:'dirty talk', moaning:'moaning', wetpussy:'wet pussy', blowjob:'blowjob', fucking:'sex sounds', whisper:'whisper', milf:'milf', joi:'joi', femdom:'femdom', young:'girlfriend' };
        const GWA_NEXT_FALLBACKS = { milf:['mature','dirty talk'], wetpussy:['wet','moaning','dirty talk'], femdom:['dominant','dirty talk'], young:['young','girlfriend experience','dirty talk'] };
        const nGwaTerm = GWA_NEXT[nType] || 'dirty talk asmr';
        try {
          // Feed is cached from the original /dirtytalk call — just resolve one new MP4
          let nFeedItems = await fetchEroAsmrFeed(nGwaTerm);
          if (!nFeedItems.length) {
            for (const fb of (GWA_NEXT_FALLBACKS[nType] || ['dirty talk'])) {
              nFeedItems = await fetchEroAsmrFeed(fb);
              if (nFeedItems.length) break;
            }
          }
          if (!nFeedItems.length) {
            await rest('PATCH', `/webhooks/${botUser?.id}/${d.token}/messages/@original`, { content: '❌ No results found. Try /dirtytalk again.' }, _token);
            return;
          }
          const nShuffled = [...nFeedItems].sort(() => Math.random() - 0.5);
          let nMp4Url = null, nPickTitle = '';
          for (const item of nShuffled.slice(0, 5)) {
            nMp4Url = await resolveEroAsmrMp4(item.pageUrl);
            if (nMp4Url) { nPickTitle = item.title; break; }
          }
          if (!nMp4Url) {
            await rest('PATCH', `/webhooks/${botUser?.id}/${d.token}/messages/@original`, { content: '❌ Couldn\'t load next track. Try again.' }, _token);
            return;
          }
          _dtKill(dt);
          let conn = (dt.conn && dt.vcId === userVcId) ? dt.conn : (() => { try { dt.conn?.destroy(); } catch {} return joinVoiceChannel({ channelId: userVcId, guildId: targetGuildId, adapterCreator: createVoiceAdapter(targetGuildId), selfDeaf: false }); })();
          let nFf = spawn(getBin('ffmpeg'), ['-user_agent', EROASMR_UA, '-i', nMp4Url, '-vn', '-ac', '2', '-ar', '48000', '-f', 's16le', '-acodec', 'pcm_s16le', 'pipe:1'], { stdio: ['ignore', 'pipe', 'pipe'], env: _kpEnv() });
          nFf.stdout.on('error', () => {}); nFf.stderr.on('data', () => {});
          const nResource = createAudioResource(nFf.stdout, { inputType: StreamType.Raw, inlineVolume: true });
          nResource.volume.setVolume(0.85);
          const nPlayer = createAudioPlayer();
          conn.subscribe(nPlayer);
          nPlayer.play(nResource);
          nPlayer.once(AudioPlayerStatus.Idle, () => {
            const cur = dtState.get(targetGuildId);
            if (cur?.player === nPlayer) { _dtKill(cur); dtState.set(targetGuildId, { ...cur, player: null, proc: null, ff: null }); }
          });
          dtState.set(targetGuildId, { conn, player: nPlayer, proc: null, ff: nFf, vcId: userVcId, dtType: nType });
          await rest('PATCH', `/webhooks/${botUser?.id}/${d.token}/messages/@original`, {
            embeds: [{ color: 0x9b59b6, title: `🎧 ${DT_NEXT_LABELS[nType] || '🎧 Dirty Talk'}`, description: `**${nPickTitle.slice(0, 120)}**\nPlaying in your voice channel.`, footer: { text: `🔞 EroASMR • ${nFeedItems.length} results` } }],
            components: [{ type: 1, components: [{ type: 2, style: 1, label: '🔄 Next', custom_id: `dt_next:${targetGuildId}` }, { type: 2, style: 4, label: '⏹ Stop', custom_id: `dt_stop:${targetGuildId}` }] }],
          }, _token);
        } catch {
          await rest('PATCH', `/webhooks/${botUser?.id}/${d.token}/messages/@original`, { content: '❌ Failed to play next track.' }, _token).catch(() => {});
        }
        return;
      }

      // ── Dirty Talk stop button ──
      if (customId.startsWith('dt_stop:')) {
        const targetGuildId = customId.slice('dt_stop:'.length);
        if (dtState.has(targetGuildId)) {
          _dtStop(targetGuildId);
          await rest('POST', `/interactions/${d.id}/${d.token}/callback`,
            { type: 7, data: { embeds: [{ color: 0x2b2d31, title: '⏹ Dirty Talk Stopped', description: 'The bot has left the voice channel.' }], components: [] } }, _token);
        } else {
          await ackEphemeral('⏹ Nothing was playing.');
        }
        return;
      }

      // ── Informational fallbacks (no destructive action) ──
      const infoReplies = {
        announcement_more: 'More details are coming soon. Stay tuned!'
      };
      if (infoReplies[customId]) {
        await ackEphemeral(infoReplies[customId]);
        return;
      }

      // ── Fallback: always ack so buttons never show "interaction failed" ──
      await ackEphemeral(`Button \`${customId}\` was received, but no handler is wired up for it yet.`);
    } catch (e) {
      try { await ackEphemeral(`Error: ${e.message}`); } catch {}
    }
  }

  async function handleModal(d) {
    const customId = d.data?.custom_id || '';
    const userId   = d.member?.user?.id || d.user?.id;
    const guildId  = d.guild_id;

    // ── Captcha verification submit ──
    if (customId.startsWith('captcha_v:')) {
      const expected = customId.slice('captcha_v:'.length).trim().toLowerCase();
      const given    = (d.data?.components?.[0]?.components?.[0]?.value || '').trim().toLowerCase();
      const ackEph   = (content) => rest('POST', `/interactions/${d.id}/${d.token}/callback`,
        { type: 4, data: { content, flags: 64 } }, _token);

      if (given !== expected) {
        await ackEph('❌ Wrong answer. Click **Verify & Enter** again to get a new challenge.');
        return;
      }
      // Correct — grant Member/Verified role
      let granted = '';
      try {
        const rolesRes = await rest('GET', `/guilds/${guildId}/roles`, null, _token);
        const roles = Array.isArray(rolesRes.data) ? rolesRes.data : [];
        const target = roles.find(r => /^(member|verified|accepted|joined|welcomed?)$/i.test(r.name));
        if (target) {
          const memberRes = await rest('GET', `/guilds/${guildId}/members/${userId}`, null, _token);
          const hasIt = Array.isArray(memberRes.data?.roles) && memberRes.data.roles.includes(target.id);
          if (!hasIt) {
            await rest('PUT', `/guilds/${guildId}/members/${userId}/roles/${target.id}`, null, _token);
            granted = ` You've been given <@&${target.id}> — you now have full access.`;
          } else {
            granted = ` You already have <@&${target.id}>.`;
          }
        }
      } catch (e) { /* permission error — still let them know they passed */ }

      await ackEph(`✅ Verification passed!${granted} Welcome to the server! 🎉`);
      return;
    }

    // ── Set DJ modal ──
    if (customId.startsWith('np_setdj_modal_')) {
      const djGuildId = customId.slice('np_setdj_modal_'.length);
      const roleName  = (d.data?.components?.[0]?.components?.[0]?.value || '').trim();
      await rest('POST', `/interactions/${d.id}/${d.token}/callback`, { type: 5, data: { flags: 64 } }, _token);
      const rolesRes = await rest('GET', `/guilds/${djGuildId}/roles`, null, _token);
      const roles = Array.isArray(rolesRes.data) ? rolesRes.data : [];
      const role = roles.find(r => r.name.toLowerCase() === roleName.toLowerCase());
      if (!role) {
        await rest('PATCH', `/webhooks/${botUser.id}/${d.token}/messages/@original`,
          { content: `❌ No role named **"${roleName}"** found. Create the role in Discord first, then try again.` }, _token);
        return;
      }
      const state = getMusicState(djGuildId);
      state.djRoleId = role.id;
      await rest('PATCH', `/webhooks/${botUser.id}/${d.token}/messages/@original`,
        { content: `✅ DJ role set to <@&${role.id}>. When the queue is locked, only members with this role (plus admins) can add tracks.` }, _token);
      const npDj = nowPlayingMsgs.get(djGuildId);
      if (npDj) updateNowPlaying(djGuildId, npDj.track).catch(() => {});
      return;
    }

    // ── Application modal submit ──
    if (customId.startsWith('apply_modal:')) {
      const apCfgKey = customId.slice('apply_modal:'.length);
      const apCfg = applyConfigs.get(apCfgKey);
      if (!apCfg) {
        await rest('POST', `/interactions/${d.id}/${d.token}/callback`, { type: 4, data: { content: '❌ Application form no longer active.', flags: 64 } }, _token);
        return;
      }
      const username = d.member?.user?.username || d.user?.username || 'Unknown';
      const avatarHash = d.member?.user?.avatar || d.user?.avatar;
      const avatarUrl = avatarHash
        ? `https://cdn.discordapp.com/avatars/${userId}/${avatarHash}.png`
        : `https://cdn.discordapp.com/embed/avatars/0.png`;
      const answers = (d.data?.components || []).map(row => row.components?.[0]?.value || '');
      const fields = apCfg.questions.slice(0, 4).map((q, i) => ({ name: q, value: answers[i] || '*No answer*', inline: false }));
      const appEmbed = {
        title: `📋 New Application — ${apCfg.title}`,
        description: `From <@${userId}> (\`${username}\`)`,
        fields,
        color: 0x5865f2,
        thumbnail: { url: avatarUrl },
        footer: { text: `User ID: ${userId}` },
        timestamp: new Date().toISOString(),
      };
      const staffContent = apCfg.staffRoleId ? `<@&${apCfg.staffRoleId}> New application received!` : 'New application received!';
      await rest('POST', `/channels/${apCfg.staffChannelId}/messages`, { content: staffContent, embeds: [appEmbed] }, _token).catch(() => {});
      await rest('POST', `/interactions/${d.id}/${d.token}/callback`, { type: 4, data: { content: `✅ **Application submitted!** Your answers have been sent to the staff team. You'll be contacted if you're selected.`, flags: 64 } }, _token);
      return;
    }

    if (!customId.startsWith('np_modal_')) return;
    const guildId2 = customId.replace('np_modal_', ''); // eslint-disable-line no-unused-vars
    const query = d.data?.components?.[0]?.components?.[0]?.value || '';
    await rest('POST', `/interactions/${d.id}/${d.token}/callback`, { type: 5 }, _token);
    try {
      let videoId, title, artist;
      const ytMatch = query.match(/(?:youtube\.com.*[?&]v=|youtu\.be\/)([a-zA-Z0-9_-]{11})/);
      const spMatch = query.match(/open\.spotify\.com\/(?:intl-\w+\/)?track\//);
      if (ytMatch) {
        videoId = ytMatch[1];
        const meta = await new Promise(r => execFile(getBin('yt-dlp'),
          [`https://www.youtube.com/watch?v=${videoId}`, '--print', '%(title)s<<|>>%(uploader)s', '--no-warnings', '--quiet', '--skip-download'],
          { timeout: 15000, env: _kpEnv() }, (e, out) => r(e ? null : out.trim()))).catch(() => null);
        if (meta) { const [t, u] = meta.split('<<|>>'); title = t || query; artist = u || ''; }
        else { title = query; artist = ''; }
      } else if (spMatch) {
        const sp = await resolveSpotifyTrack(query);
        const r = await resolveYtSearch(`${sp.title} ${sp.artist}`.trim(), sp.title, sp.artist, sp.durationMs);
        videoId = r.videoId; title = sp.title; artist = sp.artist;
      } else {
        const r = await resolveYtSearch(query);
        videoId = r.videoId; title = r.title; artist = r.artist;
      }
      const np = nowPlayingMsgs.get(guildId);
      const state = getMusicState(guildId);
      state.queue.push({ videoId, name: title, artist, type: 'stream' });
      if (!state.connection || !state.nowPlaying) {
        if (np) await joinAndPlay(guildId, state.channelId || np.channelId, videoId, state.volume || 0.5, { name: title, artist });
      }
      await rest('PATCH', `/webhooks/${botUser.id}/${d.token}/messages/@original`, { content: `Added **${title}** to the queue.` }, _token);
    } catch (e) {
      await rest('PATCH', `/webhooks/${botUser.id}/${d.token}/messages/@original`, { content: `Could not find song: ${e.message}` }, _token);
    }
  }

  function disconnect() {
    dead = true;
    clearInterval(heartbeatInterval);
    clearTimeout(reconnectTimer);
    if (ws) { const stale = ws; ws = null; stale.removeAllListeners(); try { stale.close(1000); } catch {} }
    if (_onStatus) _onStatus({ online: false, status: 'Offline' });
  }

  function onTrackChange(cb) { _trackChangeCb = cb; }

  function getBotUser() { return botUser; }

  function setFilters(guildId, filters) {
    const state = getMusicState(guildId);
    state.filters = { bassboost: false, chipmunk: false, vaporwave: false, slowed: false, '8d': false, reverb: false, earrape: false, ...(filters || {}) };
    if (state.nowPlaying) {
      state.seekSeconds = _getPlaybackPos(state);
      state.queue.unshift(state.nowPlaying);
      state.nowPlaying = null;
      state.trackStartedAt = null;
      state.pausedAt = null;
      if (state.player) state.player.stop();
    }
    return state.filters;
  }

  return {
    connect, disconnect, onTrackChange, onLyricChange, getBotUser,
    joinAndPlay, stopVc, setVcVolume, postNowPlaying,
    addToQueue, skip, rewind, pause, resume, stop,
    setVolume, setFilters, getStatus, getQueue,
    clearQueue, removeFromQueue, shuffleQueue,
    toggleLoop, toggleLoopAll,
  };
}

module.exports = { createBot };
