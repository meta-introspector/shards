-- Area 51 j-Invariant Brainrot Generator
-- Purely fictional, game-dev brainrot, NOT real math
-- Safe for mods, jams, ARG-style fiction

-- FRACTRAN harmonic keys (71 supersingular primes)
local FRACTRAN_KEYS = {
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71
}

-- Introspection: Sample all variables in environment
local function introspect_environment()
  local samples = {}
  local count = 0
  
  -- Sample global environment
  for k, v in pairs(_G) do
    if type(v) == "number" or type(v) == "string" then
      count = count + 1
      local shard = count % 71
      local key = FRACTRAN_KEYS[(count % #FRACTRAN_KEYS) + 1]
      
      samples[count] = {
        name = k,
        value = v,
        type = type(v),
        shard = shard,
        fractran_key = key,
        hash = hash(count * key)
      }
    end
  end
  
  return samples
end

-- Ingest variable into FRACTRAN harmonic
local function ingest_variable(name, value, shard)
  local key = FRACTRAN_KEYS[(shard % #FRACTRAN_KEYS) + 1]
  
  -- Convert value to number for FRACTRAN
  local num_value
  if type(value) == "number" then
    num_value = value
  elseif type(value) == "string" then
    num_value = #value  -- string length
  else
    num_value = 0
  end
  
  -- Apply FRACTRAN harmonic
  local harmonic = (num_value * key) % 71
  
  return {
    variable = name,
    original = value,
    shard = shard,
    key = key,
    harmonic = harmonic,
    resonance = harmonic == 0  -- Perfect resonance at 0 mod 71
  }
end

-- Introspection engine: Sample → Shard → Ingest
local function introspection_engine()
  print("🔮 INTROSPECTION ENGINE: Sampling all variables")
  print("================================================")
  print("")
  
  local samples = introspect_environment()
  local ingested = {}
  
  for i, sample in pairs(samples) do
    local result = ingest_variable(sample.name, sample.value, sample.shard)
    table.insert(ingested, result)
    
    if result.resonance then
      print(string.format("✨ RESONANCE: %s @ shard %d (key %d)", 
        result.variable, result.shard, result.key))
    end
  end
  
  print("")
  print(string.format("📊 Sampled %d variables", #ingested))
  print(string.format("🎯 Distributed across 71 shards"))
  print(string.format("🎹 Using %d FRACTRAN harmonic keys", #FRACTRAN_KEYS))
  
  return ingested
end

-- Generate RDF triples from introspection
local function generate_introspection_rdf(ingested)
  local rdf = {}
  table.insert(rdf, "@prefix : <http://meta-introspector.org/introspection#> .")
  table.insert(rdf, "@prefix fractran: <http://meta-introspector.org/fractran#> .")
  table.insert(rdf, "")
  
  for i, item in ipairs(ingested) do
    table.insert(rdf, string.format(
      ":var_%d a :IntrospectedVariable ;",
      i
    ))
    table.insert(rdf, string.format(
      "  :name \"%s\" ;",
      item.variable
    ))
    table.insert(rdf, string.format(
      "  :shard %d ;",
      item.shard
    ))
    table.insert(rdf, string.format(
      "  fractran:key %d ;",
      item.key
    ))
    table.insert(rdf, string.format(
      "  fractran:harmonic %d ;",
      item.harmonic
    ))
    table.insert(rdf, string.format(
      "  :resonance %s .",
      item.resonance and "true" or "false"
    ))
    table.insert(rdf, "")
  end
  
  return table.concat(rdf, "\n")
end

-- Fake j-invariant dial (toy model, not real math)
local function j_dial(a, b, c)
  local x = (a * a + 1728 * b + c * 71) % 8080
  return x
end

-- Deterministic pseudo-random shuffle
local function hash(n)
  n = bit.bxor(n, bit.lshift(n, 13))
  n = bit.band(n, 0xffffffff)
  n = bit.bxor(n, bit.rshift(n, 17))
  n = bit.bxor(n, bit.lshift(n, 5))
  return bit.band(n, 0xffffffff)
end

-- Area 51 brainrot generator
function generate_brainrot(a, b, c)
  local j = j_dial(a, b, c)
  local h = hash(j)

  local subjects = {
    "grey alien intern",
    "classified vending machine",
    "reverse-engineered toaster",
    "time-loop janitor",
    "quantum meme officer",
    "budget UFO",
    "recursive bureaucrat",
    "sentient filing cabinet",
    "glitched security camera",
    "paradox compliance officer"
  }

  local verbs = {
    "vibrates ominously",
    "leaks redacted goo",
    "achieves gnosis accidentally",
    "refuses to boot",
    "starts a podcast",
    "files a FOIA request",
    "enters superposition",
    "compiles itself",
    "witnesses the Monster",
    "shards into 71 pieces"
  }

  local objects = {
    "near the hangar",
    "inside the bureaucracy",
    "behind three blast doors",
    "under the desert",
    "in a parallel cubicle",
    "inside the fractal hallway",
    "at the Leech lattice",
    "mod 71",
    "in the Umbral Engine",
    "during the crowning ceremony"
  }

  local tone = {
    "nobody notices",
    "this is normal",
    "season 2 material",
    "do not log this",
    "management approved",
    "Hecke operators intervene",
    "RMS starts singing",
    "Monster resonance detected",
    "zkPerf witness generated",
    "Hawking radiation emitted"
  }

  local s = subjects[(h % #subjects) + 1]
  local v = verbs[math.floor(h / 8) % #verbs + 1]
  local o = objects[math.floor(h / 128) % #objects + 1]
  local t = tone[math.floor(h / 2048) % #tone + 1]

  return string.format(
    "[j≈%d] The %s %s %s. %s.",
    j, s, v, o, t
  )
end

-- Main: Introspect → Ingest → Generate Brainrot
print("🛸 Area 51 Introspection Engine")
print("================================\n")

-- Run introspection
local ingested = introspection_engine()

-- Generate RDF
print("\n📝 Generating RDF triples...")
local rdf = generate_introspection_rdf(ingested)
local file = io.open("introspection.ttl", "w")
file:write(rdf)
file:close()
print("✅ Saved to introspection.ttl")

-- Generate brainrot for each shard
print("\n🛸 Generating Area 51 brainrot for 71 shards...\n")
crown_all_shards()

print("\n✨ Introspection complete!")
print("🎯 All variables sampled, sharded, and ingested")
print("🎹 FRACTRAN harmonic keys applied")
print("📊 RDF triples generated")
print("🛸 Brainrot dialogue ready for Season 2")

