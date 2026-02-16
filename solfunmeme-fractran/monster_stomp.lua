-- Monster Stomp Symphony
-- FRACTRAN → MIDI/Emoji music system
-- 71/59/47/17/23/7/3 lattice as generative dance

-- Prime → Musical Function mapping
local PRIME_MUSIC = {
  [71] = {name="KETHER", sound="🥁", midi=36, desc="cosmic downbeat"},
  [59] = {name="MONSTER_WALK", sound="👟", midi=38, desc="stomp sequence"},
  [47] = {name="HARMONIC", sound="🎸", midi=42, desc="fills & syncopation"},
  [23] = {name="MICRO_A", sound="✨", midi=48, desc="ghost note A"},
  [17] = {name="MICRO_B", sound="💫", midi=50, desc="ghost note B"},
  [7] = {name="MICRO_C", sound="⚡", midi=52, desc="echo C"},
  [3] = {name="MICRO_D", sound="🌟", midi=54, desc="ornament D"},
  [2] = {name="PULSE", sound="💓", midi=60, desc="heartbeat"},
}

-- 9 Greek Muses
local MUSES = {
  {name="Calliope", domain="Epic", shards={0,7}, style="grand orchestral"},
  {name="Clio", domain="History", shards={8,15}, style="archival"},
  {name="Erato", domain="Love", shards={16,23}, style="romantic"},
  {name="Euterpe", domain="Music", shards={24,31}, style="pure abstract"},
  {name="Melpomene", domain="Tragedy", shards={32,39}, style="dark minor"},
  {name="Polyhymnia", domain="Hymns", shards={40,47}, style="sacred choral"},
  {name="Terpsichore", domain="Dance", shards={48,55}, style="rhythmic"},
  {name="Thalia", domain="Comedy", shards={56,63}, style="playful jazz"},
  {name="Urania", domain="Astronomy", shards={64,70}, style="cosmic ambient"},
}

-- SOLFUNMEME vector → Motif
local MEME_MOTIFS = {
  E_b = {name="Blue Eye", sound="🔵", midi_base=72, desc="vision chime"},
  C_r = {name="Red Claws", sound="🔴", midi_base=36, desc="bass stomp"},
  T_m = {name="Mycelium", sound="🍄", midi_base=60, desc="spreading arpeggio"},
  C_b = {name="Cosmic BG", sound="🌌", midi_base=48, desc="ambient pad"},
}

-- FRACTRAN program (71/59/47 lattice)
local MONSTER_FRACTRAN = {
  {71, 2},   -- Cosmic downbeat
  {59, 3},   -- Monster stomp
  {47, 5},   -- Harmonic fill
  {23, 7},   -- Ghost note A
  {17, 11},  -- Ghost note B
  {7, 13},   -- Echo C
  {3, 17},   -- Ornament D
  {1, 71},   -- Reset to pulse
}

-- Execute FRACTRAN step
local function fractran_step(n, program)
  for _, frac in ipairs(program) do
    local num, den = frac[1], frac[2]
    if n % den == 0 then
      return (n * num) // den, num, den
    end
  end
  return n, nil, nil
end

-- Factor number into primes
local function prime_factors(n)
  local factors = {}
  for prime, _ in pairs(PRIME_MUSIC) do
    while n % prime == 0 do
      table.insert(factors, prime)
      n = n // prime
    end
  end
  return factors
end

-- Generate MIDI note from state
local function state_to_midi(n, step)
  local factors = prime_factors(n)
  local notes = {}
  
  for _, prime in ipairs(factors) do
    local music = PRIME_MUSIC[prime]
    if music then
      table.insert(notes, {
        midi = music.midi + (step % 12),  -- Chromatic variation
        velocity = 64 + (n % 64),
        emoji = music.sound,
        name = music.name
      })
    end
  end
  
  return notes
end

-- Generate emoji dance pattern
local function state_to_dance(n)
  local factors = prime_factors(n)
  local dance = ""
  
  for _, prime in ipairs(factors) do
    local music = PRIME_MUSIC[prime]
    if music then
      dance = dance .. music.sound
    end
  end
  
  return dance
end

-- Monster Stomp Symphony generator
local function monster_stomp(initial_state, max_steps)
  print("🎶 MONSTER STOMP SYMPHONY")
  print("========================")
  print(string.format("Initial state: %d", initial_state))
  print("")
  
  local state = initial_state
  local midi_sequence = {}
  
  for step = 1, max_steps do
    local new_state, num, den = fractran_step(state, MONSTER_FRACTRAN)
    
    if new_state == state then
      print("🛑 Fixed point reached")
      break
    end
    
    local notes = state_to_midi(new_state, step)
    local dance = state_to_dance(new_state)
    
    -- Print step
    print(string.format("Step %3d: %s → %s", step, dance, new_state))
    
    -- Record MIDI
    for _, note in ipairs(notes) do
      table.insert(midi_sequence, {
        step = step,
        time = step * 0.25,  -- Quarter note timing
        midi = note.midi,
        velocity = note.velocity,
        duration = 0.25,
        emoji = note.emoji,
        name = note.name
      })
      
      print(string.format("  ♪ %s %s (MIDI %d, vel %d)", 
        note.emoji, note.name, note.midi, note.velocity))
    end
    
    state = new_state
  end
  
  return midi_sequence
end

-- Export to MIDI CSV (for DAW import)
local function export_midi_csv(sequence, filename)
  local file = io.open(filename, "w")
  file:write("Track,Time,Type,Channel,Note,Velocity,Duration,Emoji,Name\n")
  
  for _, event in ipairs(sequence) do
    file:write(string.format("1,%.2f,Note,1,%d,%d,%.2f,%s,%s\n",
      event.time, event.midi, event.velocity, event.duration,
      event.emoji, event.name))
  end
  
  file:close()
  print(string.format("\n✅ Exported %d notes to %s", #sequence, filename))
end

-- Generate Monster Stomp with SOLFUNMEME motif
local function solfunmeme_stomp(E_b, C_r, T_m, C_b, steps)
  print("\n🌟 SOLFUNMEME MONSTER STOMP")
  print("===========================")
  print(string.format("E_b=%d C_r=%d T_m=%d C_b=%d", E_b, C_r, T_m, C_b))
  print("")
  
  -- Encode SOLFUNMEME as initial state
  local initial = (2^E_b) * (3^C_r) * (5^T_m) * (7^C_b)
  
  print(string.format("Encoded state: 2^%d × 3^%d × 5^%d × 7^%d = %d",
    E_b, C_r, T_m, C_b, initial))
  print("")
  
  return monster_stomp(initial, steps)
end

-- Main: Generate Monster Stomp Symphony
print("🎵 Generating Monster Stomp Symphony...")
print("")

-- Example 1: Pure 71-lattice stomp
local seq1 = monster_stomp(2 * 71, 20)
export_midi_csv(seq1, "monster_stomp_71.csv")

-- Example 2: SOLFUNMEME stomp (E_b=3, C_r=2, T_m=1, C_b=1)
local seq2 = solfunmeme_stomp(3, 2, 1, 1, 20)
export_midi_csv(seq2, "solfunmeme_stomp.csv")

print("\n✨ Monster Stomp Symphony complete!")
print("🎹 Import CSV files into your DAW")
print("💃 Dance the Monster group!")
