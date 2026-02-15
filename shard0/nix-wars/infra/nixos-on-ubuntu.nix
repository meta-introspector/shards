{
  description = "NixOS-on-Ubuntu: Port Nix-Wars to Ubuntu with systemd";
  
  outputs = { self }:
    let
      # Ubuntu systemd service for Nix-Wars
      systemdService = ''
        [Unit]
        Description=Nix-Wars Game Server
        After=network.target nginx.service
        
        [Service]
        Type=simple
        User=www-data
        WorkingDirectory=/var/www/nixwars
        ExecStart=/usr/bin/python3 -m http.server 8080
        Restart=always
        RestartSec=10
        
        # Security
        NoNewPrivileges=true
        PrivateTmp=true
        ProtectSystem=strict
        ProtectHome=true
        ReadWritePaths=/var/www/nixwars
        
        [Install]
        WantedBy=multi-user.target
      '';
      
      # Ubuntu nginx config
      nginxConfig = ''
        server {
          listen 80;
          server_name nixwars.local;
          
          location / {
            proxy_pass http://localhost:8080;
            proxy_set_header Host $host;
            proxy_set_header X-Real-IP $remote_addr;
          }
        }
      '';
      
      # Installation script for Ubuntu
      installScript = ''
        #!/usr/bin/env bash
        set -e
        
        echo "🐧 Installing Nix-Wars on Ubuntu"
        echo "================================="
        echo ""
        
        # Install Nix
        if ! command -v nix &> /dev/null; then
          echo "📦 Installing Nix..."
          curl -L https://nixos.org/nix/install | sh -s -- --daemon
          . /etc/profile.d/nix.sh
        fi
        
        # Install dependencies
        echo "📦 Installing dependencies..."
        sudo apt-get update
        sudo apt-get install -y nginx python3 jq curl
        
        # Deploy game
        echo "🎮 Deploying game..."
        sudo mkdir -p /var/www/nixwars
        sudo cp -r docs/* /var/www/nixwars/
        sudo chown -R www-data:www-data /var/www/nixwars
        
        # Install systemd service
        echo "⚙️  Installing systemd service..."
        sudo tee /etc/systemd/system/nixwars.service > /dev/null << 'EOF'
        ${systemdService}
        EOF
        
        sudo systemctl daemon-reload
        sudo systemctl enable nixwars
        sudo systemctl start nixwars
        
        # Configure nginx
        echo "🌐 Configuring nginx..."
        sudo tee /etc/nginx/sites-available/nixwars > /dev/null << 'EOF'
        ${nginxConfig}
        EOF
        
        sudo ln -sf /etc/nginx/sites-available/nixwars /etc/nginx/sites-enabled/
        sudo nginx -t && sudo systemctl reload nginx
        
        # Generate witness
        echo "⚡ Generating deployment witness..."
        bash witness-deployment.sh http://localhost:8080
        
        echo ""
        echo "✅ Installation complete!"
        echo ""
        echo "🎮 Play at: http://localhost/"
        echo "📊 Status: sudo systemctl status nixwars"
        echo "📝 Logs: sudo journalctl -u nixwars -f"
      '';
      
      # Verification script
      verifyScript = ''
        #!/usr/bin/env bash
        set -e
        
        echo "🔍 Verifying Nix-Wars deployment"
        echo "================================="
        echo ""
        
        # Check systemd service
        if systemctl is-active --quiet nixwars; then
          echo "✅ Service running"
        else
          echo "❌ Service not running"
          exit 1
        fi
        
        # Check nginx
        if systemctl is-active --quiet nginx; then
          echo "✅ Nginx running"
        else
          echo "❌ Nginx not running"
          exit 1
        fi
        
        # Check endpoints
        for endpoint in / /bbs.html /url-only.html; do
          STATUS=$(curl -s -o /dev/null -w "%{http_code}" "http://localhost$endpoint")
          if [ "$STATUS" = "200" ]; then
            echo "✅ $endpoint: $STATUS"
          else
            echo "❌ $endpoint: $STATUS"
          fi
        done
        
        # Generate witness
        bash witness-deployment.sh http://localhost
        
        echo ""
        echo "✅ Verification complete"
      '';
      
    in {
      packages.x86_64-linux.default = {
        systemdService = systemdService;
        nginxConfig = nginxConfig;
        installScript = installScript;
        verifyScript = verifyScript;
      };
      
      # Ubuntu deployment bundle
      ubuntuBundle = builtins.toFile "install-ubuntu.sh" installScript;
      verifyBundle = builtins.toFile "verify-ubuntu.sh" verifyScript;
    };
}
