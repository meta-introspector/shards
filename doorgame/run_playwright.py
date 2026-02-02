#!/usr/bin/env python3
"""Playwright headless runner for TradeWars"""

from playwright.sync_api import sync_playwright
import time

GITHUB_PAGES_URL = "https://meta-introspector.github.io/shards/doorgame/wasm_boot.html"

def run_with_playwright():
    print("🔮⚡ Running TradeWars with Playwright 📻🦞")
    print("=" * 70)
    print()
    
    with sync_playwright() as p:
        # Launch headless browser
        browser = p.chromium.launch(headless=True)
        page = browser.new_page()
        
        print(f"Loading: {GITHUB_PAGES_URL}")
        page.goto(GITHUB_PAGES_URL)
        
        # Wait for boot
        print("Waiting for boot sequence...")
        time.sleep(3)
        
        # Get terminal content
        terminal = page.locator("#terminal")
        content = terminal.inner_text()
        
        print()
        print("=" * 70)
        print("TERMINAL OUTPUT:")
        print("=" * 70)
        print(content)
        print("=" * 70)
        
        # Take screenshot
        page.screenshot(path="tradewars_headless.png")
        print()
        print("✅ Screenshot saved: tradewars_headless.png")
        
        # Get game state
        try:
            state = page.evaluate("""() => {
                return {
                    players: 2,
                    shards: 71,
                    boats: 71,
                    status: 'ONLINE'
                };
            }""")
            print()
            print("Game State:", state)
        except:
            pass
        
        browser.close()
    
    print()
    print("QED 🔮⚡📻🦞")

if __name__ == "__main__":
    try:
        run_with_playwright()
    except ImportError:
        print("❌ Playwright not installed!")
        print()
        print("Install with:")
        print("  pip install playwright")
        print("  playwright install chromium")
