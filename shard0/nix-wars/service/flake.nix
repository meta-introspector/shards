{
  description = "Nix-Wars as a pure functional service";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      
      # Pure functional service definition
      nixwarsService = {
        name = "nixwars";
        port = 8080;
        domain = "solana.solfunmeme.com";
        
        # Static site content
        content = pkgs.stdenv.mkDerivation {
          name = "nixwars-content";
          src = ../docs;
          
          installPhase = ''
            mkdir -p $out
            cp -r $src/* $out/
            
            # Generate state file
            cat > $out/state.json << EOF
            {
              "round": 0,
              "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
              "games": ["tournament", "bbs", "url", "flying", "modern", "pilot"]
            }
            EOF
          '';
        };
        
        # Nginx configuration as pure function
        nginxConfig = port: domain: root: ''
          server {
            listen ${toString port};
            server_name ${domain};
            
            root ${root};
            index play.html index.html;
            
            location / {
              try_files $uri $uri/ =404;
              add_header Cache-Control "no-cache";
              add_header Access-Control-Allow-Origin "*";
            }
            
            location ~ \.json$ {
              add_header Content-Type application/json;
            }
            
            location ~ \.html$ {
              add_header X-Frame-Options "SAMEORIGIN";
            }
          }
        '';
        
        # Systemd service as pure function
        systemdService = name: content: ''
          [Unit]
          Description=Nix-Wars Game Server
          After=network.target nginx.service
          Requires=nginx.service
          
          [Service]
          Type=oneshot
          RemainAfterExit=yes
          ExecStart=${pkgs.bash}/bin/bash -c 'ln -sf ${content} /var/www/${name}'
          ExecStop=${pkgs.bash}/bin/bash -c 'rm -f /var/www/${name}'
          
          [Install]
          WantedBy=multi-user.target
        '';
      };
      
      # Mapping function: NixOS service -> Ubuntu systemd
      toSystemd = service: pkgs.writeTextDir "systemd/${service.name}.service" 
        (service.systemdService service.name service.content);
      
      # Mapping function: NixOS nginx -> Ubuntu nginx
      toNginx = service: pkgs.writeTextDir "nginx/${service.name}.conf"
        (service.nginxConfig service.port service.domain service.content);
      
    in {
      packages.${system} = {
        # The content
        content = nixwarsService.content;
        
        # Systemd service file
        systemd = toSystemd nixwarsService;
        
        # Nginx config file
        nginx = toNginx nixwarsService;
        
        # Complete deployment package
        default = pkgs.stdenv.mkDerivation {
          name = "nixwars-service";
          
          buildInputs = [ pkgs.bash ];
          
          unpackPhase = "true";
          
          installPhase = ''
            mkdir -p $out/bin
            
            # Install script
            cat > $out/bin/install-nixwars << 'EOF'
            #!/usr/bin/env bash
            set -e
            
            CONTENT="${nixwarsService.content}"
            SYSTEMD="${toSystemd nixwarsService}/systemd/${nixwarsService.name}.service"
            NGINX="${toNginx nixwarsService}/nginx/${nixwarsService.name}.conf"
            
            echo "🚀 Installing Nix-Wars as systemd service"
            echo "=========================================="
            echo ""
            
            # Install systemd service
            echo "📦 Installing systemd service..."
            sudo cp "$SYSTEMD" /etc/systemd/system/${nixwarsService.name}.service
            sudo systemctl daemon-reload
            
            # Install nginx config
            echo "⚙️  Installing nginx config..."
            sudo cp "$NGINX" /etc/nginx/sites-available/${nixwarsService.name}.conf
            sudo ln -sf /etc/nginx/sites-available/${nixwarsService.name}.conf \
                        /etc/nginx/sites-enabled/${nixwarsService.name}.conf
            
            # Enable and start service
            echo "🔄 Enabling service..."
            sudo systemctl enable ${nixwarsService.name}.service
            sudo systemctl start ${nixwarsService.name}.service
            
            # Reload nginx
            echo "🔄 Reloading nginx..."
            sudo nginx -t && sudo systemctl reload nginx
            
            echo ""
            echo "✅ Installation complete!"
            echo ""
            echo "🎮 Access at:"
            echo "   http://${nixwarsService.domain}:${toString nixwarsService.port}/play.html"
            echo ""
            echo "📊 Service status:"
            sudo systemctl status ${nixwarsService.name}.service --no-pager
            EOF
            
            chmod +x $out/bin/install-nixwars
            
            # Uninstall script
            cat > $out/bin/uninstall-nixwars << 'EOF'
            #!/usr/bin/env bash
            set -e
            
            echo "🗑️  Uninstalling Nix-Wars service"
            
            sudo systemctl stop ${nixwarsService.name}.service || true
            sudo systemctl disable ${nixwarsService.name}.service || true
            sudo rm -f /etc/systemd/system/${nixwarsService.name}.service
            sudo rm -f /etc/nginx/sites-enabled/${nixwarsService.name}.conf
            sudo rm -f /etc/nginx/sites-available/${nixwarsService.name}.conf
            sudo systemctl daemon-reload
            sudo systemctl reload nginx
            
            echo "✅ Uninstalled"
            EOF
            
            chmod +x $out/bin/uninstall-nixwars
          '';
        };
      };
      
      apps.${system} = {
        install = {
          type = "app";
          program = "${self.packages.${system}.default}/bin/install-nixwars";
        };
        
        uninstall = {
          type = "app";
          program = "${self.packages.${system}.default}/bin/uninstall-nixwars";
        };
      };
    };
}
