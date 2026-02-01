#!/usr/bin/env bash
# create-dmz-nodes.sh - Create 23 isolated network namespaces

set -euo pipefail

echo "Creating 23-node DMZ architecture..."

# Create DMZ bridge
if ! ip link show dmz-bridge &>/dev/null; then
    brctl addbr dmz-bridge
    ip link set dmz-bridge up
    ip addr add 10.71.255.1/16 dev dmz-bridge
    echo "Created DMZ bridge at 10.71.255.1"
fi

# Create 23 isolated nodes
for node in {0..22}; do
    # Skip if namespace exists
    if ip netns list | grep -q "node${node}"; then
        echo "Node ${node} already exists, skipping"
        continue
    fi
    
    # Create network namespace
    ip netns add node${node}
    
    # Create veth pair
    ip link add veth${node} type veth peer name veth${node}-br
    
    # Move one end into namespace
    ip link set veth${node} netns node${node}
    
    # Configure namespace interface
    ip netns exec node${node} ip addr add 10.71.${node}.1/24 dev veth${node}
    ip netns exec node${node} ip link set veth${node} up
    ip netns exec node${node} ip link set lo up
    
    # Configure bridge end
    ip link set veth${node}-br up
    brctl addif dmz-bridge veth${node}-br
    
    # Calculate shards for this node
    shard1=$node
    shard2=$((node + 23))
    shard3=$((node + 46))
    
    echo "Created node ${node} at 10.71.${node}.1 (shards: ${shard1}, ${shard2}, ${shard3})"
done

# Enable audit logging via iptables
iptables -A FORWARD -j LOG --log-prefix "DMZ-AUDIT: " --log-level 4 2>/dev/null || true

# Create audit log directory
mkdir -p /var/log/dmz
touch /var/log/dmz/audit.log
chmod 600 /var/log/dmz/audit.log

echo ""
echo "DMZ world created successfully!"
echo "  23 nodes: node0 - node22"
echo "  71 shards distributed across nodes"
echo "  Audit log: /var/log/dmz/audit.log"
echo ""
echo "Test connectivity:"
echo "  ip netns exec node0 ping -c 1 10.71.1.1"
echo ""
echo "Start Erlang node:"
echo "  ip netns exec node0 erl -sname node0 -setcookie monster71"
