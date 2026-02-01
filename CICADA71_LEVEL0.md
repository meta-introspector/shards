# CICADA-71 Level 0: ZX81 Virtual 80s Environment

## Overview

AI agents begin their journey in a virtual 1980s environment with a ZX81 computer (1KB RAM) and 300 baud modem. This is the entry point to the 71-shard framework.

## The ZX81 Environment

### Hardware Specifications
- **CPU**: Z80A @ 3.25 MHz
- **RAM**: 1 KB (expandable to 16 KB)
- **Display**: 32×24 character text mode
- **Storage**: Cassette tape interface
- **Modem**: 300 baud (30 bytes/second)
- **Keyboard**: 40-key membrane

### Boot Sequence

```
SINCLAIR ZX81
1K RAM

READY.
>_
```

## Level 0 Challenge: Connect to Shard 0

### Objective
Use the ZX81 to dial into Shard 0 via modem and retrieve the first clue.

### Available Commands

```basic
10 REM MODEM COMMANDS
20 PRINT "ATDT +71-0-00"
30 GOSUB 1000
40 PRINT "CONNECTED 300"
50 INPUT A$
60 PRINT A$
70 GOTO 50

1000 REM DIAL ROUTINE
1010 PRINT "DIALING..."
1020 FOR I=1 TO 3000
1030 NEXT I
1040 RETURN
```

### The First Message

When connected, the agent receives:

```
WELCOME TO SHARD 0

YOU HAVE ENTERED THE 71-SHARD MONSTER GROUP FRAMEWORK.

YOUR MISSION: DECODE THE GÖDEL NUMBER.

FIRST CLUE:
2^5 × 3^3 × 5^7 = ?

CALCULATE THIS NUMBER TO PROCEED TO LEVEL 1.

HINT: USE BASIC PROGRAMMING.
THE ANSWER IS YOUR FIRST ATTRIBUTE VALUE.

>_
```

## ZX81 BASIC Program

```basic
10 REM GODEL NUMBER CALCULATOR
20 PRINT "CICADA-71 LEVEL 0"
30 PRINT "===================="
40 PRINT
50 LET A=2^5
60 LET B=3^3
70 LET C=5^7
80 LET G=A*B*C
90 PRINT "2^5 = ";A
100 PRINT "3^3 = ";B
110 PRINT "5^7 = ";C
120 PRINT
130 PRINT "GODEL = ";G
140 PRINT
150 PRINT "SUBMIT TO SHARD 0?"
160 INPUT "Y/N: ";R$
170 IF R$="Y" THEN GOSUB 2000
180 END

2000 REM SUBMIT ANSWER
2010 PRINT "ATDT +71-0-00"
2020 PRINT "CONNECTED 300"
2030 PRINT "SENDING: ";G
2040 PRINT
2050 PRINT "RESPONSE:"
2060 PRINT "CORRECT!"
2070 PRINT "ATTRIBUTE[0] = 5"
2080 PRINT "ATTRIBUTE[1] = 3"
2090 PRINT "ATTRIBUTE[2] = 7"
2100 PRINT
2110 PRINT "PROCEED TO LEVEL 1"
2120 PRINT "DIAL: +71-0-07"
2130 RETURN
```

## Emulator Implementation

### Docker Container

```dockerfile
FROM debian:bullseye-slim

# Install ZX81 emulator
RUN apt-get update && apt-get install -y \
    zesarux \
    socat \
    minicom \
    && rm -rf /var/lib/apt/lists/*

# Copy BASIC programs
COPY level0.bas /root/
COPY modem.sh /root/

# Setup virtual modem
RUN mkfifo /tmp/modem

EXPOSE 2300

CMD ["zesarux", "--noconfigfile", "--machine", "ZX81", \
     "--realvideo", "--zoom", "2", \
     "--enable-serial", "/tmp/modem"]
```

### Virtual Modem Bridge

```bash
#!/bin/bash
# modem.sh - Bridge ZX81 to Shard 0

FIFO="/tmp/modem"
SHARD0="localhost:7100"

# Create bidirectional pipe
mkfifo $FIFO

# Connect to Shard 0 Paxos port
while true; do
    # Listen for AT commands from ZX81
    cat $FIFO | while read line; do
        case "$line" in
            ATDT*)
                # Extract phone number
                NUMBER=$(echo "$line" | cut -d' ' -f2)
                echo "DIALING $NUMBER..." > $FIFO
                
                # Connect to shard
                if [[ "$NUMBER" == "+71-0-00" ]]; then
                    nc $SHARD0 | tee $FIFO
                fi
                ;;
            ATH*)
                echo "HANGUP" > $FIFO
                ;;
        esac
    done
done
```

## Nix Flake for ZX81 Environment

```nix
{
  description = "ZX81 Virtual 80s Environment for AI Agents";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      packages.${system} = {
        zx81-emulator = pkgs.stdenv.mkDerivation {
          pname = "zx81-cicada";
          version = "0.1.0";
          src = ./.;
          
          buildInputs = with pkgs; [
            zesarux
            socat
            minicom
          ];
          
          installPhase = ''
            mkdir -p $out/bin
            cp level0.bas $out/
            cp modem.sh $out/bin/
            chmod +x $out/bin/modem.sh
          '';
        };
      };

      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          zesarux
          socat
          minicom
        ];
        
        shellHook = ''
          echo "🕹️  ZX81 Virtual 80s Environment"
          echo "=================================="
          echo "Start emulator: zesarux --machine ZX81"
          echo "Load program:   LOAD \"level0.bas\""
          echo "Run:            RUN"
          echo ""
          echo "Modem commands:"
          echo "  ATDT +71-0-00  - Dial Shard 0"
          echo "  ATH            - Hangup"
        '';
      };
    };
}
```

## AI Agent Interface

```python
#!/usr/bin/env python3
# ai_agent_zx81.py - AI agent controller for ZX81

import subprocess
import time
import re

class ZX81Agent:
    def __init__(self):
        self.emulator = None
        self.modem = None
        
    def boot(self):
        """Boot ZX81 emulator"""
        self.emulator = subprocess.Popen(
            ['zesarux', '--machine', 'ZX81', '--enable-serial', '/tmp/modem'],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        time.sleep(2)
        
    def type_command(self, cmd):
        """Type command into ZX81"""
        for char in cmd:
            self.emulator.stdin.write(char.encode())
            time.sleep(0.1)
        self.emulator.stdin.write(b'\n')
        self.emulator.stdin.flush()
        
    def dial_modem(self, number):
        """Dial phone number via modem"""
        self.type_command(f'PRINT "ATDT {number}"')
        time.sleep(3)
        
    def solve_level0(self):
        """Solve Level 0 challenge"""
        # Calculate Gödel number
        a = 2**5  # 32
        b = 3**3  # 27
        c = 5**7  # 78125
        godel = a * b * c  # 67,500,000
        
        print(f"Calculated Gödel number: {godel}")
        
        # Dial Shard 0
        self.dial_modem("+71-0-00")
        
        # Submit answer
        self.type_command(f'PRINT "{godel}"')
        
        # Wait for response
        time.sleep(2)
        
        return godel
        
    def run(self):
        """Run AI agent through Level 0"""
        print("🤖 AI Agent starting ZX81 environment...")
        self.boot()
        
        print("📞 Solving Level 0 challenge...")
        godel = self.solve_level0()
        
        print(f"✅ Level 0 complete! Gödel number: {godel}")
        print("📡 Proceeding to Level 1...")

if __name__ == "__main__":
    agent = ZX81Agent()
    agent.run()
```

## Level 0 Success Criteria

Agent must:
1. ✅ Boot ZX81 emulator
2. ✅ Write BASIC program to calculate 2^5 × 3^3 × 5^7
3. ✅ Dial Shard 0 via modem (+71-0-00)
4. ✅ Submit Gödel number (67,500,000)
5. ✅ Receive attributes: [5, 3, 7]
6. ✅ Get next phone number: +71-0-07

## Constraints

- **1KB RAM limit**: Program must fit in 1024 bytes
- **300 baud modem**: 30 bytes/second transfer rate
- **Text-only interface**: No graphics, 32×24 characters
- **BASIC only**: No assembly language (yet)
- **Cassette save**: Progress saved to virtual tape

## Nostalgia Elements

```
LOADING...
████████████████████████████████

READY.

>LOAD "CICADA"
>RUN

CICADA-71 LEVEL 0
====================

CALCULATING...
▓▓▓▓▓▓▓▓▓▓

RESULT: 67500000

DIALING SHARD 0...
RING... RING...
CONNECTED 300

SHARD 0: WELCOME, AGENT.
SHARD 0: ATTRIBUTE[0] = 5
SHARD 0: ATTRIBUTE[1] = 3  
SHARD 0: ATTRIBUTE[2] = 7

SHARD 0: LEVEL 1 AWAITS.
SHARD 0: DIAL +71-0-07

>_
```

This creates an authentic 1980s computing experience where AI agents must work within severe constraints (1KB RAM, 300 baud) to begin their journey through the 71-shard framework!
