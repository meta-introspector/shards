#!/bin/bash
# Monster Arcade BBS Door Launcher
# Usage: ./monster_arcade_door.sh [node_number] [username]

NODE=${1:-1}
USER=${2:-SYSOP}

echo "Monster Arcade BBS Door"
echo "Node: $NODE | User: $USER"
echo ""

# Run the game
./target/release/monster-arcade

# Return to BBS
exit 0
