#!/usr/bin/env python3
"""Run TradeWars in headless browser from GitHub Pages"""

import subprocess
import sys
import time

GITHUB_PAGES_URL = "https://meta-introspector.github.io/shards/doorgame/wasm_boot.html"

def run_headless():
    print("🔮⚡ Running TradeWars in Headless Browser 📻🦞")
    print("=" * 70)
    print()
    print(f"URL: {GITHUB_PAGES_URL}")
    print()
    
    # Try different headless browsers
    browsers = [
        # Chrome/Chromium headless
        ["chromium", "--headless", "--disable-gpu", "--dump-dom", GITHUB_PAGES_URL],
        ["google-chrome", "--headless", "--disable-gpu", "--dump-dom", GITHUB_PAGES_URL],
        ["chromium-browser", "--headless", "--disable-gpu", "--dump-dom", GITHUB_PAGES_URL],
        
        # Firefox headless
        ["firefox", "--headless", "--screenshot", GITHUB_PAGES_URL],
        
        # Playwright (if installed)
        ["playwright", "screenshot", GITHUB_PAGES_URL, "tradewars.png"],
    ]
    
    for browser_cmd in browsers:
        try:
            print(f"Trying: {browser_cmd[0]}...")
            result = subprocess.run(
                browser_cmd,
                capture_output=True,
                text=True,
                timeout=10
            )
            
            if result.returncode == 0:
                print(f"✅ Success with {browser_cmd[0]}!")
                print()
                print("Output:")
                print(result.stdout[:1000])  # First 1000 chars
                return True
                
        except FileNotFoundError:
            print(f"  ⚠️  {browser_cmd[0]} not found")
        except subprocess.TimeoutExpired:
            print(f"  ⚠️  {browser_cmd[0]} timeout")
        except Exception as e:
            print(f"  ⚠️  {browser_cmd[0]} error: {e}")
    
    print()
    print("❌ No headless browser found!")
    print()
    print("Install one of:")
    print("  - chromium-browser")
    print("  - google-chrome")
    print("  - firefox")
    print("  - playwright (pip install playwright)")
    print()
    return False

if __name__ == "__main__":
    success = run_headless()
    sys.exit(0 if success else 1)
