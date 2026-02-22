.PHONY: test lint check

test:
	cargo test

lint:
	cargo clippy -- -D warnings

check: test lint

