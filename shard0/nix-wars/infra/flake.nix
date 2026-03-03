{
  description = "Nix-Wars: DNS/VPN/Nginx/SELinux Infrastructure";
  
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  
  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      
      # DNS configuration for 71 zones
      dnsZones = builtins.genList (i: {
        zone = "zone${toString i}.nixwars.local";
        ip = "10.71.${toString (i / 256)}.${toString (i % 256)}";
      }) 71;
      
      # Generate DNS zone files
      dnsConfig = pkgs.writeText "nixwars-zones.conf" ''
        ${builtins.concatStringsSep "\n" (map (z: ''
          zone "${z.zone}" {
            type master;
            file "/var/lib/bind/db.${z.zone}";
          };
        '') dnsZones)}
      '';
      
      # Nginx configuration
      nginxConfig = pkgs.writeText "nixwars-nginx.conf" ''
        user nginx;
        worker_processes auto;
        
        events {
          worker_connections 1024;
        }
        
        http {
          # Rate limiting
          limit_req_zone $binary_remote_addr zone=nixwars:10m rate=10r/s;
          
          # Upstream for 71 zones
          ${builtins.concatStringsSep "\n" (map (z: ''
            upstream zone${toString z.zone} {
              server ${z.ip}:8080;
            }
          '') dnsZones)}
          
          # Main server
          server {
            listen 80;
            listen [::]:80;
            server_name nixwars.local *.nixwars.local;
            
            # SELinux context
            selinux_context system_u:object_r:httpd_sys_content_t:s0;
            
            # Rate limiting
            limit_req zone=nixwars burst=20 nodelay;
            
            # Static files
            location / {
              root /var/www/nixwars;
              index index.html;
              try_files $uri $uri/ =404;
            }
            
            # Game states (read-only)
            location /states/ {
              alias /nix/store/;
              autoindex on;
              add_header X-Content-Type-Options nosniff;
            }
            
            # UUCP spool (restricted)
            location /uucp/ {
              deny all;
            }
            
            # zkPerf witnesses
            location /witnesses/ {
              root /var/www/nixwars;
              add_header Content-Type application/json;
            }
          }
          
          # Zone-specific servers
          ${builtins.concatStringsSep "\n" (map (i: 
            let z = builtins.elemAt dnsZones i; in ''
            server {
              listen 80;
              server_name ${z.zone};
              
              location / {
                proxy_pass http://zone${toString i};
                proxy_set_header Host $host;
                proxy_set_header X-Real-IP $remote_addr;
              }
            }
          '') (builtins.genList (x: x) 71))}
        }
      '';
      
      # WireGuard VPN configuration
      wireguardConfig = pkgs.writeText "nixwars-wg0.conf" ''
        [Interface]
        PrivateKey = <PRIVATE_KEY>
        Address = 10.71.0.1/16
        ListenPort = 51820
        
        # Peers for 71 zones
        ${builtins.concatStringsSep "\n" (map (i: ''
          [Peer]
          # Zone ${toString i}
          PublicKey = <PEER_${toString i}_PUBLIC_KEY>
          AllowedIPs = 10.71.${toString (i / 256)}.${toString (i % 256)}/32
        '') (builtins.genList (x: x) 71))}
      '';
      
      # SELinux policy module
      selinuxPolicy = pkgs.writeText "nixwars.te" ''
        policy_module(nixwars, 1.0.0)
        
        require {
          type httpd_t;
          type httpd_sys_content_t;
          type user_home_t;
          class file { read getattr open };
          class dir { read search };
        }
        
        # Allow nginx to read Nix store
        allow httpd_t user_home_t:dir { read search };
        allow httpd_t user_home_t:file { read getattr open };
        
        # Allow access to game states
        allow httpd_t httpd_sys_content_t:file { read getattr open };
      '';
      
    in {
      packages.${system} = {
        default = pkgs.runCommand "nixwars-infra" {} ''
          mkdir -p $out/{dns,nginx,vpn,selinux}
          
          cp ${dnsConfig} $out/dns/zones.conf
          cp ${nginxConfig} $out/nginx/nixwars.conf
          cp ${wireguardConfig} $out/vpn/wg0.conf
          cp ${selinuxPolicy} $out/selinux/nixwars.te
          
          # Generate install script
          cat > $out/install.sh << 'EOF'
          #!/usr/bin/env bash
          set -e
          
          echo "🔧 Installing Nix-Wars Infrastructure"
          
          # DNS
          echo "📡 Setting up DNS..."
          sudo cp dns/zones.conf /etc/bind/
          sudo systemctl restart bind9
          
          # Nginx
          echo "🌐 Setting up Nginx..."
          sudo cp nginx/nixwars.conf /etc/nginx/sites-available/
          sudo ln -sf /etc/nginx/sites-available/nixwars.conf /etc/nginx/sites-enabled/
          sudo nginx -t && sudo systemctl restart nginx
          
          # WireGuard
          echo "🔐 Setting up VPN..."
          sudo cp vpn/wg0.conf /etc/wireguard/
          sudo systemctl enable wg-quick@wg0
          sudo systemctl start wg-quick@wg0
          
          # SELinux
          echo "🛡️  Setting up SELinux..."
          sudo checkmodule -M -m -o selinux/nixwars.mod selinux/nixwars.te
          sudo semodule_package -o selinux/nixwars.pp -m selinux/nixwars.mod
          sudo semodule -i selinux/nixwars.pp
          
          echo "✅ Infrastructure installed!"
          EOF
          
          chmod +x $out/install.sh
        '';
        
        dns-only = dnsConfig;
        nginx-only = nginxConfig;
        vpn-only = wireguardConfig;
        selinux-only = selinuxPolicy;
      };
      
      nixosModules.default = { config, lib, pkgs, ... }: {
        services.bind = {
          enable = true;
          extraConfig = builtins.readFile dnsConfig;
        };
        
        services.nginx = {
          enable = true;
          appendHttpConfig = builtins.readFile nginxConfig;
        };
        
        networking.wireguard.interfaces.wg0 = {
          ips = [ "10.71.0.1/16" ];
          listenPort = 51820;
          privateKeyFile = "/etc/wireguard/private.key";
        };
        
        boot.kernelModules = [ "wireguard" ];
      };
    };
}
