#!/usr/bin/env bash
# Quick deploy to local nginx

set -e

DOCS_DIR="$(cd "$(dirname "$0")/../docs" && pwd)"
NGINX_ROOT="/var/www/nixwars"

echo "🚀 Deploying Nix-Wars to local nginx"
echo "======================================"
echo ""

# Create nginx root
echo "📁 Creating nginx directory..."
sudo mkdir -p "$NGINX_ROOT"

# Copy game files
echo "📦 Copying game files..."
sudo cp -r "$DOCS_DIR"/* "$NGINX_ROOT/"

# Set permissions
echo "🔐 Setting permissions..."
sudo chown -R www-data:www-data "$NGINX_ROOT" 2>/dev/null || sudo chown -R nginx:nginx "$NGINX_ROOT" 2>/dev/null || true
sudo chmod -R 755 "$NGINX_ROOT"

# Create minimal nginx config
echo "⚙️  Creating nginx config..."
sudo tee /etc/nginx/sites-available/nixwars.conf > /dev/null << 'EOF'
server {
    listen 8080;
    server_name localhost;
    
    root /var/www/nixwars;
    index index.html bbs.html;
    
    location / {
        try_files $uri $uri/ =404;
        add_header Cache-Control "no-cache";
    }
    
    location ~ \.json$ {
        add_header Content-Type application/json;
    }
}
EOF

# Enable site
echo "🔗 Enabling site..."
sudo ln -sf /etc/nginx/sites-available/nixwars.conf /etc/nginx/sites-enabled/nixwars.conf 2>/dev/null || true

# Test nginx config
echo "✅ Testing nginx config..."
sudo nginx -t

# Reload nginx
echo "🔄 Reloading nginx..."
sudo systemctl reload nginx 2>/dev/null || sudo nginx -s reload

echo ""
echo "✅ Deployment complete!"
echo ""
echo "🎮 Play the game:"
echo "   http://localhost:8080/bbs.html          (ZX81 BBS)"
echo "   http://localhost:8080/index.html        (Modern UI)"
echo "   http://localhost:8080/url-only.html     (URL-only)"
echo "   http://localhost:8080/flying-fractran.html  (Flying + FRACTRAN)"
echo ""
echo "📊 View witnesses:"
echo "   http://localhost:8080/zkperf-witnesses/"
echo ""
