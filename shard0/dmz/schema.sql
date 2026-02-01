CREATE TABLE IF NOT EXISTS dmz_audit (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    timestamp INTEGER NOT NULL,
    channel TEXT NOT NULL,
    from_node INTEGER NOT NULL,
    to_node INTEGER NOT NULL,
    from_shard INTEGER,
    to_shard INTEGER,
    size INTEGER,
    duration INTEGER,
    metadata TEXT,
    hash TEXT
);

CREATE INDEX IF NOT EXISTS idx_timestamp ON dmz_audit(timestamp);
CREATE INDEX IF NOT EXISTS idx_channel ON dmz_audit(channel);
CREATE INDEX IF NOT EXISTS idx_nodes ON dmz_audit(from_node, to_node);

-- Insert initial test entry
INSERT INTO dmz_audit (timestamp, channel, from_node, to_node, size, metadata)
VALUES (strftime('%s', 'now'), 'system', 0, 0, 0, '{"event": "dmz_initialized"}');
