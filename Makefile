# Rocqeteer pipeline (kb/runbooks/build-and-validate.md).
# Targets mirror the runbook; each gates the next.

.PHONY: all smoke rocq gen-fast build-fast test ci-checks clean

all: smoke rocq gen-fast build-fast test ci-checks ## full pipeline

smoke: ## day-zero gate: rocq theory builds, extraction round-trip, effects runtime compiles
	dune build theories/ extraction/ runtime/
	@echo "SMOKE OK: rocq + extraction + OCaml-effects wiring build on this toolchain"

rocq: ## build all Rocq theories (and proofs, once present)
	dune build theories/

gen-fast: ## run rocq-eff-codegen -> generated/
	dune build generated/

build-fast: ## compile generated direct-style OCaml + runtime + codegen
	dune build generated/ runtime/ codegen/ support/

test: ## differential tests (reference vs fast)
	dune test

ci-checks: build-fast ## TCB / forbidden-API gates
	./ci/check_no_objmagic.sh
	./ci/check_no_bind_in_generated.sh
	./ci/check_no_stray_perform.sh

clean: ## remove build artifacts
	dune clean
