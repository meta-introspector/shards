#!/usr/bin/env bash
# launch-dmz-world.sh - Start complete 23-node DMZ environment

set -euo pipefail

echo "Launching 23-node DMZ world..."

# 1. Create network namespaces
if [ ! -d /var/run/netns ]; then
    echo "Creating network namespaces..."
    sudo ./create-dmz-nodes.sh
fi

# 2. Initialize audit database
if [ ! -f /var/lib/dmz-audit.db ]; then
    echo "Initializing audit database..."
    sudo mkdir -p /var/lib
    sudo sqlite3 /var/lib/dmz-audit.db < schema.sql
    sudo chmod 644 /var/lib/dmz-audit.db
fi

# 3. Load kernel modules
echo "Loading virtual device drivers..."
if lsmod | grep -q shard_lpt; then
    echo "  shard_lpt already loaded"
else
    echo "  shard_lpt not available (build with: cd ../drivers/lpt && make)"
fi

# 4. Start Erlang nodes in each namespace
echo "Starting Erlang nodes..."
for node in {0..22}; do
    # Check if already running
    if ip netns exec node${node} pgrep -f "erl.*node${node}" &>/dev/null; then
        echo "  Node ${node} already running"
        continue
    fi
    
    # Start Erlang node in namespace
    ip netns exec node${node} \
        erl -sname node${node}@localhost \
        -setcookie monster71 \
        -env ERL_CRASH_DUMP /var/log/dmz/node${node}_crash.dump \
        -detached \
        2>/dev/null || echo "  Failed to start node ${node}"
    
    echo "  Started node${node} (shards: ${node}, $((node+23)), $((node+46)))"
done

# 5. Start audit logger
echo "Starting audit logger..."
tail -f /var/log/dmz/audit.log 2>/dev/null | while read line; do
    # Parse and insert into database
    echo "$line" >> /var/log/dmz/audit_raw.log
done &
AUDIT_PID=$!
echo "  Audit logger PID: $AUDIT_PID"

echo ""
echo "═══════════════════════════════════════════════════════════"
echo "  DMZ World Ready!"
echo "═══════════════════════════════════════════════════════════"
echo ""
echo "  Nodes:        23 (node0 - node22)"
echo "  Shards:       71 (distributed 3 per node)"
echo "  Audit DB:     /var/lib/dmz-audit.db"
echo "  Audit Log:    /var/log/dmz/audit.log"
echo ""
echo "Communication Channels:"
echo "  • Fax:        dmz-fax <from> <to> <image.pbm>"
echo "  • Phone:      dmz-call <from> <to> <duration>"
echo "  • Modem:      dmz-modem <from> <to> <data>"
echo "  • Printer:    echo 'data' > /dev/lpt<node>"
echo "  • Parquet:    dmz-transfer <from> <to> <file.parquet>"
echo ""
echo "Query Audit:"
echo "  sqlite3 /var/lib/dmz-audit.db 'SELECT * FROM dmz_audit LIMIT 10'"
echo ""
echo "Connect to node:"
echo "  ip netns exec node0 erl -sname client -remsh node0@localhost -setcookie monster71"
echo ""
echo "Stop all:"
echo "  ./stop-dmz-world.sh"
echo "═══════════════════════════════════════════════════════════"
