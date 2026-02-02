#!/bin/bash
# Send SIGINT with return code 71 (ROOSTER_CROW)
# The rooster signals the ship!

PID=$1

if [ -z "$PID" ]; then
    echo "Usage: $0 <pid>"
    exit 71
fi

echo "🐓 Sending ROOSTER CROW signal (71) to PID $PID"
echo "📻 Message: THE_ROOSTER_HAS_CROWED"
echo "🔮 Monster Walk: 0x1F90"
echo ""

# Send SIGINT
kill -INT $PID

# Return code 71
exit 71
