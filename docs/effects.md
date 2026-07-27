# The effect families

Twenty-five operations over one explicit `world`, grouped into eleven families. Every family has a
compiled, proven example in the [effects gallery](../examples/README.md), built with
`dune build examples/`, and a theory file carrying the general laws.

| Effect | Ops | One line | Tower | Gallery |
|---|---|---|---|---|
| **Keyed store** | `OGet` · `OPut` · `ODelete` | bytes-keyed state; per-key frame clauses | kernel | [`KeyedStore.v`](../examples/KeyedStore.v) |
| **Expiry** | `OSetDeadline` · `OGetDeadline` | per-binding TTLs; live iff `now ≤ deadline`, expired means absent | **derived** ([`Elab.v`](../theories/Elab.v)) | [`Expiry.v`](../examples/Expiry.v) |
| **Time** | `ONow` | one injected instant per run: deterministic by construction, replayable | kernel | [`Clock.v`](../examples/Clock.v) |
| **Errors** | `OThrow` | aborting exceptions with structured payloads; pre-throw effects commit | kernel | [`Throw.v`](../examples/Throw.v) |
| **Environment** | `OAsk` | the Reader: immutable request and configuration context | kernel | [`Ask.v`](../examples/Ask.v) |
| **Trace** | `OTrace` | the Writer: provable, ordered, structured logging | kernel | [`Tracing.v`](../examples/Tracing.v) |
| **Cache** | `OCacheGet` · `OCachePut` | a memo table invisible to the observable, so "only an optimisation" is structural | **derived** ([`ElabNs.v`](../theories/ElabNs.v)) | [`Memo.v`](../examples/Memo.v) |
| **Journal** | `OJournal` | write-only timestamped log; a proven frame law makes durability an afterthought | **derived** ([`ElabNs.v`](../theories/ElabNs.v)) | [`Journaling.v`](../examples/Journaling.v) |
| **Files** | `OOpen` · `ORead` · `OFWrite` · `OClose` | byte streams over descriptors on a pure in-world filesystem; EOF is the empty chunk; modelled errors are values; the OS seam is named and runtime-checked | kernel ([ADR-0017](../kb/architecture/decisions/adr-0017-file-io.md)) | [`Files.v`](../examples/Files.v) |
| **Sockets** | `OAccept` · `ORecv` · `OSend` · `OCloseConn` | scripted connections as the determinism-by-injection oracle; one-shot half-close contract; the proven HTTP/1.0 server rides on top | kernel ([ADR-0018](../kb/architecture/decisions/adr-0018-sockets.md)) | [`Sockets.v`](../examples/Sockets.v) |
| **Concurrency** | `OSpawn` · `OYield` · `OChanMake` · `OChanSend` · `OChanRecv` | cooperative fibers over one shared world; an injected schedule is the determinism oracle; channels the only sharing (no data races representable); deadlock is a value, never a hang | kernel ([ADR-0019](../kb/architecture/decisions/adr-0019-concurrency.md)) | [`Concurrency.v`](../examples/Concurrency.v) |

The concurrency family is realized by a cooperative scheduler over OCaml 5 `Effect.Deep`
(`runtime/sched.ml` — one-shot continuations, channels, no Eio dependency). Its faithfulness
rests on the CEK step machine ([`theories/Cek.v`](../theories/Cek.v)), a defunctionalized
continuation over the *same* `tm`, proven to agree with big-step `run` on the concurrency-free
fragment so the proven oracle is preserved; `Sched.conc_free_embeds` lifts that agreement into the
scheduler and `SchedHttp.drv_concurrent_matches` recovers the sequential HTTP transcript under it.
The realizer is validated by `tests/diff_sched.ml` (native scheduler vs the extracted `run_sched`
over proven and adversarial schedules) and `tests/diff_sched_http.ml` (the concurrent server over
real TCP); `tools/rhttpd_conc` serves real clients with the same fibers. See
[ADR-0019](../kb/architecture/decisions/adr-0019-concurrency.md).

## Effect towers

The derived families are not irreducible trust. Each has a proven elaboration into programs
over the kernel families (a plain never-expiring store, the clock, errors, environment,
trace, files), with a machine-checked refinement theorem per layer: `Elab.elab_simulates` and
`ElabNs.elab_ns_simulates`, both axiom-free and without side conditions.

A build can therefore run in **mode K**, the elaborated programs against kernel realizers
only: no deadline logic, no cache realizer, no journal realizer in the trusted runtime. That
configuration is differentially tested on every run (`diff_store_k`, `diff_cache_k`,
`diff_journal_k`), and the tower's composition with the file and socket families is checked by the
mode-K legs of `diff_file` and `diff_sock` (the `wc` counter and the HTTP buffer run through the
escaped kernel store while the real file / TCP ops pass through).

The fused realizers remain the **mode F** production default, as performance options. They
are trusted and adversarially tested, never load-bearing for the semantics. Every trusted
entry's status, `kernel-v1` or `derived(<theorem>)`, is recorded in the
[runtime manifest](runtime_manifest.toml) and surfaced in the generated
[TCB report](tcb_report.md).

## The glue

General `Match` over tagged values, the bounded `Repeat` loop, the `Fold` list eliminator,
and the checked primitives, where overflow and parse failure yield an option rather than
garbage, have their own gallery entry: [`Combinators.v`](../examples/Combinators.v).

On top of the instance theorems, a shallow weakest-precondition program logic
([`theories/Logic.v`](../theories/Logic.v), zero added trust) supports specifications with
universal quantification. See [`theories/LogicDemo.v`](../theories/LogicDemo.v).
