
-- LMFDB Monster Prime Walk Schema

CREATE TABLE monster_primes (
    prime_id SERIAL PRIMARY KEY,
    prime_value INTEGER NOT NULL,
    prime_index INTEGER NOT NULL,
    topo_class INTEGER NOT NULL CHECK (topo_class >= 0 AND topo_class < 10)
);

CREATE TABLE harmonic_layers (
    layer_id SERIAL PRIMARY KEY,
    prime_id INTEGER REFERENCES monster_primes(prime_id),
    frequency INTEGER NOT NULL,
    amplitude DOUBLE PRECISION NOT NULL,
    phase DOUBLE PRECISION NOT NULL,
    data_hash BYTEA NOT NULL
);

CREATE TABLE bit_patterns (
    pattern_id SERIAL PRIMARY KEY,
    prime_id INTEGER REFERENCES monster_primes(prime_id),
    pattern_value BIGINT NOT NULL,
    occurrence_count INTEGER NOT NULL,
    entropy DOUBLE PRECISION NOT NULL
);

CREATE TABLE perf_metrics (
    metric_id SERIAL PRIMARY KEY,
    algorithm_name TEXT NOT NULL,
    prime_id INTEGER REFERENCES monster_primes(prime_id),
    execution_time_ns BIGINT NOT NULL,
    memory_bytes BIGINT NOT NULL,
    cpu_cycles BIGINT NOT NULL
);

CREATE TABLE j_invariants (
    j_id SERIAL PRIMARY KEY,
    layer_set INTEGER[] NOT NULL,
    j_value INTEGER NOT NULL CHECK (j_value < 196884),
    computed_at TIMESTAMP DEFAULT NOW()
);

CREATE INDEX idx_harmonic_prime ON harmonic_layers(prime_id);
CREATE INDEX idx_bit_pattern_prime ON bit_patterns(prime_id);
CREATE INDEX idx_perf_prime ON perf_metrics(prime_id);
