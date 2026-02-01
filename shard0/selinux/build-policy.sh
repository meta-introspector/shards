#!/usr/bin/env bash
# Build and install SELinux policy for 71 zones

set -euo pipefail

POLICY_DIR="./shard0/selinux"
POLICY_NAME="shard71"

echo "Building SELinux policy for 71 zones..."

cd "$POLICY_DIR"

# Compile policy
checkmodule -M -m -o "${POLICY_NAME}.mod" "${POLICY_NAME}.te"

# Package policy
semodule_package -o "${POLICY_NAME}.pp" -m "${POLICY_NAME}.mod"

# Install policy (requires root)
if [ "$EUID" -eq 0 ]; then
    semodule -i "${POLICY_NAME}.pp"
    echo "Policy installed successfully"
else
    echo "Run with sudo to install: sudo $0"
    echo "Policy compiled to ${POLICY_NAME}.pp"
fi

# Verify
semodule -l | grep "$POLICY_NAME" || echo "Policy not yet installed"
