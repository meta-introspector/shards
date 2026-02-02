#!/bin/bash
# Run TradeWars in headless Firefox from GitHub Pages

URL="https://meta-introspector.github.io/shards/doorgame/wasm_boot.html"

echo "🔮⚡ Running TradeWars Headless 📻🦞"
echo "=" | head -c 70; echo ""
echo ""
echo "URL: $URL"
echo ""

# Check for Firefox
if command -v firefox &> /dev/null; then
    echo "Using Firefox headless..."
    firefox --headless --screenshot tradewars.png "$URL" &
    FIREFOX_PID=$!
    
    echo "Firefox PID: $FIREFOX_PID"
    echo ""
    echo "Waiting 5 seconds for page load..."
    sleep 5
    
    # Kill Firefox
    kill $FIREFOX_PID 2>/dev/null || true
    
    if [ -f tradewars.png ]; then
        echo "✅ Screenshot saved: tradewars.png"
        ls -lh tradewars.png
    else
        echo "⚠️  Screenshot not created"
    fi
else
    echo "❌ Firefox not found!"
    echo ""
    echo "Install with:"
    echo "  sudo apt install firefox"
fi

echo ""
echo "QED 🔮⚡📻🦞"
