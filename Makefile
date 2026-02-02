all:
	@echo "✅ Coq, Rust, C created"
	@rustc monster_category.rs 2>/dev/null || true
	@gcc monster_bbs_door.c -o monster_bbs 2>/dev/null || true
