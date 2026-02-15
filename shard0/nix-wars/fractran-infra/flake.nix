{
  description = "FRACTRAN -> Nix -> Infrastructure: Pure functional deployment";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      
      # FRACTRAN program encoding game state
      fractran = {
        # 71×59×47 universe encoded as FRACTRAN fractions
        universe = [
          { num = 71; den = 1; }   # Layer
          { num = 59; den = 1; }   # Sector  
          { num = 47; den = 1; }   # Zone
        ];
        
        # Current state as prime factorization
        # state = 2^round × 3^players × 5^games
        initialState = 2 * 3 * 5;  # Round 0, 1 player, 1 game
        
        # State transitions as FRACTRAN fractions
        transitions = [
          { num = 3; den = 2; }    # Add player: multiply by 3/2
          { num = 5; den = 1; }    # Add game: multiply by 5
          { num = 2; den = 1; }    # Next round: multiply by 2
        ];
      };
      
      # Nix expression derived from FRACTRAN
      nixConfig = fractran: {
        # Extract parameters from FRACTRAN
        layers = builtins.elemAt fractran.universe 0;
        sectors = builtins.elemAt fractran.universe 1;
        zones = builtins.elemAt fractran.universe 2;
        
        # Compute derived values
        totalSlots = (builtins.elemAt fractran.universe 0).num * 
                     (builtins.elemAt fractran.universe 1).num * 
                     (builtins.elemAt fractran.universe 2).num;
        
        # Service configuration
        service = {
          name = "nixwars";
          port = 8080;
          domain = "solana.solfunmeme.com";
          ipv6 = "fd00::71:59:47";  # From FRACTRAN primes
        };
      };
      
      config = nixConfig fractran;
      
      # Mapping: Nix -> Systemd
      toSystemd = cfg: pkgs.writeText "nixwars.service" ''
        [Unit]
        Description=Nix-Wars Game Server (FRACTRAN-derived)
        After=network.target nginx.service
        Requires=nginx.service
        
        [Service]
        Type=oneshot
        RemainAfterExit=yes
        
        # State from FRACTRAN
        Environment="FRACTRAN_STATE=${toString fractran.initialState}"
        Environment="LAYERS=${toString config.layers.num}"
        Environment="SECTORS=${toString config.sectors.num}"
        Environment="ZONES=${toString config.zones.num}"
        
        ExecStart=${pkgs.bash}/bin/bash -c '\
          mkdir -p /var/lib/nixwars && \
          echo "{\"state\": $FRACTRAN_STATE, \"layers\": $LAYERS}" > /var/lib/nixwars/state.json && \
          ln -sf ${self.packages.${system}.content} /var/www/nixwars'
        
        ExecStop=${pkgs.bash}/bin/bash -c 'rm -f /var/www/nixwars'
        
        [Install]
        WantedBy=multi-user.target
      '';
      
      # Mapping: Nix -> Nginx
      toNginx = cfg: pkgs.writeText "nixwars.conf" ''
        server {
          listen ${toString cfg.service.port};
          server_name ${cfg.service.domain};
          
          root /var/www/nixwars;
          index play.html;
          
          # FRACTRAN state endpoint
          location /state {
            alias /var/lib/nixwars/state.json;
            add_header Content-Type application/json;
          }
          
          location / {
            try_files $uri $uri/ =404;
            add_header X-FRACTRAN-Layers "${toString cfg.layers.num}";
            add_header X-FRACTRAN-Sectors "${toString cfg.sectors.num}";
            add_header X-FRACTRAN-Zones "${toString cfg.zones.num}";
          }
        }
      '';
      
      # Mapping: Nix -> DNS (zone file)
      toDNS = cfg: pkgs.writeText "nixwars.zone" ''
        $TTL 300
        @       IN      SOA     ns1.${cfg.service.domain}. admin.${cfg.service.domain}. (
                        2026021501 ; Serial (YYYYMMDDNN)
                        3600       ; Refresh
                        1800       ; Retry
                        604800     ; Expire
                        300 )      ; Minimum TTL
        
        @       IN      NS      ns1.${cfg.service.domain}.
        @       IN      A       192.168.68.1
        @       IN      AAAA    ${cfg.service.ipv6}
        
        ; FRACTRAN-derived subdomains
        layer${toString cfg.layers.num}   IN  CNAME  @
        sector${toString cfg.sectors.num} IN  CNAME  @
        zone${toString cfg.zones.num}     IN  CNAME  @
      '';
      
      # Mapping: Nix -> IPv6 (netplan)
      toIPv6 = cfg: pkgs.writeText "nixwars-ipv6.yaml" ''
        network:
          version: 2
          ethernets:
            eth0:
              addresses:
                - ${cfg.service.ipv6}/64
              routes:
                - to: fd00::71:0:0/48
                  via: fd00::1
      '';
      
      # Mapping: Nix -> VPN (WireGuard)
      toVPN = cfg: pkgs.writeText "nixwars-wg.conf" ''
        [Interface]
        Address = ${cfg.service.ipv6}/64
        ListenPort = ${toString (cfg.service.port + 1000)}
        PrivateKey = <GENERATED>
        
        # Peer for each layer (71 peers)
        ${builtins.concatStringsSep "\n" (builtins.genList (i: ''
          [Peer]
          PublicKey = <LAYER_${toString i}_KEY>
          AllowedIPs = fd00::71:${toString i}:0/112
        '') cfg.layers.num)}
      '';
      
      # Mapping: Nix -> SELinux policy
      toSELinux = cfg: pkgs.writeText "nixwars.te" ''
        module nixwars 1.0;
        
        require {
          type httpd_t;
          type httpd_sys_content_t;
          class file { read getattr open };
          class dir { read search open };
        }
        
        # Allow nginx to read FRACTRAN state
        allow httpd_t httpd_sys_content_t:file { read getattr open };
        allow httpd_t httpd_sys_content_t:dir { read search open };
        
        # Label for /var/lib/nixwars
        type nixwars_state_t;
        files_type(nixwars_state_t)
        allow httpd_t nixwars_state_t:file { read getattr open };
      '';
      
      # Mapping: Nix -> Terraform
      toTerraform = cfg: pkgs.writeText "nixwars.tf" ''
        terraform {
          required_providers {
            local = { source = "hashicorp/local" }
          }
        }
        
        # FRACTRAN-derived infrastructure
        locals {
          layers  = ${toString cfg.layers.num}
          sectors = ${toString cfg.sectors.num}
          zones   = ${toString cfg.zones.num}
          total   = ${toString cfg.totalSlots}
        }
        
        # Deploy systemd service
        resource "local_file" "systemd" {
          filename = "/etc/systemd/system/${cfg.service.name}.service"
          content  = file("${toSystemd cfg}")
        }
        
        # Deploy nginx config
        resource "local_file" "nginx" {
          filename = "/etc/nginx/sites-available/${cfg.service.name}.conf"
          content  = file("${toNginx cfg}")
        }
        
        # Deploy DNS zone
        resource "local_file" "dns" {
          filename = "/etc/bind/zones/${cfg.service.domain}.zone"
          content  = file("${toDNS cfg}")
        }
        
        # Deploy IPv6 config
        resource "local_file" "ipv6" {
          filename = "/etc/netplan/99-${cfg.service.name}.yaml"
          content  = file("${toIPv6 cfg}")
        }
        
        # Deploy VPN config
        resource "local_file" "vpn" {
          filename = "/etc/wireguard/${cfg.service.name}.conf"
          content  = file("${toVPN cfg}")
        }
        
        # Deploy SELinux policy
        resource "local_file" "selinux" {
          filename = "/etc/selinux/modules/${cfg.service.name}.te"
          content  = file("${toSELinux cfg}")
        }
        
        # Outputs
        output "fractran_state" {
          value = ${toString fractran.initialState}
        }
        
        output "universe_size" {
          value = local.total
        }
      '';
      
    in {
      packages.${system} = {
        # Game content
        content = pkgs.stdenv.mkDerivation {
          name = "nixwars-content";
          src = ../docs;
          installPhase = ''
            mkdir -p $out
            cp -r $src/* $out/
          '';
        };
        
        # All infrastructure files
        systemd = toSystemd config;
        nginx = toNginx config;
        dns = toDNS config;
        ipv6 = toIPv6 config;
        vpn = toVPN config;
        selinux = toSELinux config;
        terraform = toTerraform config;
        
        # Complete deployment
        default = pkgs.stdenv.mkDerivation {
          name = "nixwars-fractran-infra";
          
          unpackPhase = "true";
          
          installPhase = ''
            mkdir -p $out/{bin,infra}
            
            # Copy all infrastructure files
            cp ${toSystemd config} $out/infra/nixwars.service
            cp ${toNginx config} $out/infra/nixwars.conf
            cp ${toDNS config} $out/infra/nixwars.zone
            cp ${toIPv6 config} $out/infra/nixwars-ipv6.yaml
            cp ${toVPN config} $out/infra/nixwars-wg.conf
            cp ${toSELinux config} $out/infra/nixwars.te
            cp ${toTerraform config} $out/infra/nixwars.tf
            
            # Deployment script
            cat > $out/bin/deploy << EOF
            #!/usr/bin/env bash
            set -e
            
            INFRA="$out/infra"
            
            echo "🔢 FRACTRAN -> Nix -> Infrastructure"
            echo "====================================="
            echo ""
            echo "FRACTRAN State: ${toString fractran.initialState}"
            echo "Universe: ${toString config.layers.num}×${toString config.sectors.num}×${toString config.zones.num} = ${toString config.totalSlots}"
            echo ""
            
            # Systemd
            echo "📦 Deploying systemd..."
            sudo cp "\$INFRA/nixwars.service" /etc/systemd/system/
            sudo systemctl daemon-reload
            sudo systemctl enable nixwars.service
            sudo systemctl start nixwars.service
            
            # Nginx
            echo "⚙️  Deploying nginx..."
            sudo cp "\$INFRA/nixwars.conf" /etc/nginx/sites-available/
            sudo ln -sf /etc/nginx/sites-available/nixwars.conf /etc/nginx/sites-enabled/
            sudo nginx -t && sudo systemctl reload nginx
            
            echo ""
            echo "✅ Deployment complete!"
            echo ""
            echo "🎮 Access at:"
            echo "   http://${config.service.domain}:${toString config.service.port}/play.html"
            echo "   http://[${config.service.ipv6}]:${toString config.service.port}/play.html"
            echo ""
            echo "📊 Service status:"
            sudo systemctl status nixwars.service --no-pager || true
            EOF
            
            chmod +x $out/bin/deploy
            
            # Terraform deployment
            cat > $out/bin/terraform-deploy << 'EOF'
            #!/usr/bin/env bash
            cd $out/infra
            terraform init
            terraform apply -auto-approve
            EOF
            
            chmod +x $out/bin/terraform-deploy
          '';
        };
      };
      
      apps.${system} = {
        deploy = {
          type = "app";
          program = "${self.packages.${system}.default}/bin/deploy";
        };
        
        terraform = {
          type = "app";
          program = "${self.packages.${system}.default}/bin/terraform-deploy";
        };
      };
    };
}
