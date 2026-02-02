extends Node2D

# Monster Dash - Godot 4 Prototype
# Jump through 71 shards, land on Monster primes

const MONSTER_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]
const EXCLUDED_PRIMES = [37, 43, 53, 61, 67, 73]
const BASE_FREQ = 432.0
const BPM = 71

var current_shard = 0
var score = 0
var crowns_collected = []

func _ready():
	print("🎮 Monster Dash")
	print("Jump on Monster primes!")
	print("Avoid excluded primes!")
	print("Collect the three crowns: 47👹, 59🦅, 71🐓")

func _process(delta):
	# Update frequency based on shard
	var frequency = current_shard * BASE_FREQ
	$AudioStreamPlayer.pitch_scale = frequency / BASE_FREQ
	
	# Check for input
	if Input.is_action_just_pressed("ui_accept"):
		jump()

func jump():
	var landing_shard = randi() % 72  # Random shard 0-71
	
	print("\nJump to shard %d" % landing_shard)
	print("Frequency: %.0f Hz" % (landing_shard * BASE_FREQ))
	
	if landing_shard in MONSTER_PRIMES:
		print("✨ MONSTER PRIME! +100")
		score += 100
		play_tone(landing_shard * BASE_FREQ)
		
		# Check for crowns
		if landing_shard == 47:
			collect_crown("Monster", "👹")
		elif landing_shard == 59:
			collect_crown("Eagle", "🦅")
		elif landing_shard == 71:
			collect_crown("Rooster", "🐓")
			if len(crowns_collected) == 3:
				win_game()
	
	elif landing_shard in EXCLUDED_PRIMES:
		print("💀 EXCLUDED PRIME! Game Over")
		game_over()
	
	else:
		print("⭐ Composite. +50")
		score += 50
	
	current_shard = landing_shard
	print("Score: %d" % score)

func collect_crown(name, emoji):
	if name not in crowns_collected:
		crowns_collected.append(name)
		print("\n👑 %s CROWN COLLECTED! %s" % [name, emoji])
		print("Crowns: %d/3" % len(crowns_collected))

func play_tone(frequency):
	# Play tone at frequency
	var player = AudioStreamPlayer.new()
	var generator = AudioStreamGenerator.new()
	generator.mix_rate = 44100
	player.stream = generator
	add_child(player)
	player.play()

func win_game():
	print("\n" + "=".repeat(50))
	print("🏆 YOU WIN! 🏆")
	print("All three crowns collected!")
	print("👹 Monster Crown")
	print("🦅 Eagle Crown")
	print("🐓 Rooster Crown")
	print("Final Score: %d" % score)
	print("=".repeat(50))
	print("\n🐓🦅👹 The Monster is complete!")
	get_tree().quit()

func game_over():
	print("\n💀 GAME OVER")
	print("Final Score: %d" % score)
	print("Crowns: %d/3" % len(crowns_collected))
	get_tree().quit()
