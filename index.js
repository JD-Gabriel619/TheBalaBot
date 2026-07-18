// index.js

require("dotenv").config();

const { createBot } = require("./bot");

if (!process.env.DISCORD_BOT_TOKEN) {
    throw new Error("Missing DISCORD_BOT_TOKEN");
}

if (!process.env.DISCORD_CLIENT_ID) {
    throw new Error("Missing DISCORD_CLIENT_ID");
}

if (!process.env.GROQ_API_KEY) {
    console.warn("Warning: GROQ_API_KEY is not set.");
}

const bot = createBot();

bot.connect(process.env.DISCORD_BOT_TOKEN, (status) => {
    if (status.online) {
        console.log(`✅ Logged in as ${status.tag}`);
    } else {
        console.log(status);
    }
});