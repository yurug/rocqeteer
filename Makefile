# Rocqeteer pipeline (kb/runbooks/build-and-validate.md).
# Targets mirror the runbook; each gates the next.

.PHONY: all smoke rocq gen-fast build-fast test tcb-report ci-checks demo clean

all: smoke rocq gen-fast build-fast test tcb-report ci-checks ## full pipeline

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

tcb-report: ## regenerate docs/tcb_report.md from live build facts
	./ci/gen_tcb_report.sh

ci-checks: build-fast test ## TCB / forbidden-API gates (require the differential tests to pass)
	./ci/check_no_objmagic.sh
	./ci/check_no_bind_in_generated.sh
	./ci/check_no_stray_perform.sh
	./ci/check_no_admitted.sh
	./ci/check_generated_fresh.sh
	./ci/check_tcb.sh

demo: ## end-to-end narrated demo (audited counter) + HTML report
	dune build demo/demo.exe
	dune exec demo/demo.exe

clean: ## remove build artifacts
	dune clean
