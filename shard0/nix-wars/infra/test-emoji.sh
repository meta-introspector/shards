#!/usr/bin/env bash
# Test emoji rendering in headless browser

set -e

URL="${1:-http://solana.solfunmeme.com:8080/bbs.html}"

echo "🧪 Testing emoji rendering: $URL"
echo ""

# Create test script
cat > /tmp/test-emoji.js << 'EOF'
const puppeteer = require('puppeteer');

(async () => {
  const browser = await puppeteer.launch({
    headless: true,
    args: ['--no-sandbox', '--disable-setuid-sandbox']
  });
  
  const page = await browser.newPage();
  await page.goto(process.argv[2] || 'http://localhost:8080/bbs.html');
  
  await page.waitForTimeout(2000);
  
  // Check canvas
  const canvas = await page.$('canvas');
  if (canvas) {
    console.log('✅ Canvas found');
    
    // Get canvas dimensions
    const box = await canvas.boundingBox();
    console.log(`   Size: ${box.width}x${box.height}`);
  } else {
    console.log('❌ No canvas');
  }
  
  // Take screenshot
  await page.screenshot({ path: '/tmp/nixwars-test.png' });
  console.log('📸 Screenshot: /tmp/nixwars-test.png');
  
  // Check for errors
  page.on('console', msg => console.log('Console:', msg.text()));
  page.on('pageerror', err => console.log('Error:', err.message));
  
  await browser.close();
})();
EOF

# Run with node if available
if command -v node &> /dev/null && command -v npm &> /dev/null; then
    npm install puppeteer 2>/dev/null || true
    node /tmp/test-emoji.js "$URL"
else
    echo "⚠️  Node.js not available, trying wget..."
    wget -O /tmp/page.html "$URL"
    echo "Page downloaded: $(wc -l < /tmp/page.html) lines"
    
    # Check for emoji in HTML
    if grep -q "🚀\|🌌\|⭐" /tmp/page.html; then
        echo "✅ Emojis found in HTML"
    else
        echo "❌ No emojis in HTML"
    fi
fi
