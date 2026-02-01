#!/usr/bin/env node
/**
 * CICADA-71 Promptbook CLI
 * Run door game via Promptbook pipelines
 */

const { execSync } = require('child_process');
const fs = require('fs');
const path = require('path');

const BOOK_PATH = path.join(__dirname, 'cicada71.book.md');

function runPromptbook(playerName, targetShard) {
    console.log('🔮⚡ CICADA-71 Promptbook Runner');
    console.log('━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━');
    console.log();
    
    // Check if promptbook is installed
    try {
        execSync('which ptbk', { stdio: 'ignore' });
    } catch (e) {
        console.log('⚠️  Promptbook not found. Install with:');
        console.log('   npm install -g promptbook');
        console.log();
        return;
    }
    
    // Check if book exists
    if (!fs.existsSync(BOOK_PATH)) {
        console.log(`⚠️  Book not found: ${BOOK_PATH}`);
        return;
    }
    
    console.log(`📖 Book: ${BOOK_PATH}`);
    console.log(`👤 Player: ${playerName}`);
    console.log(`🎯 Target Shard: ${targetShard}`);
    console.log();
    
    // Run promptbook
    try {
        const cmd = `ptbk run ${BOOK_PATH} --input playerName="${playerName}" --input targetShard="${targetShard}"`;
        console.log(`🚀 Running: ${cmd}`);
        console.log();
        
        const result = execSync(cmd, { 
            encoding: 'utf8',
            stdio: 'inherit'
        });
        
        console.log();
        console.log('✅ Complete!');
        
    } catch (e) {
        console.log('❌ Error running promptbook:');
        console.log(e.message);
    }
}

// Parse CLI args
const args = process.argv.slice(2);

if (args.length === 0) {
    console.log('Usage: node promptbook_runner.js <playerName> <targetShard>');
    console.log();
    console.log('Example:');
    console.log('  node promptbook_runner.js Alice 42');
    console.log();
    process.exit(1);
}

const playerName = args[0] || 'Guest';
const targetShard = parseInt(args[1]) || 0;

runPromptbook(playerName, targetShard);
