# The effects gallery

One small, heavily-commented file per effect family. Every program here is real EffIR, every claim is
a machine-checked theorem (`vm_compute`-verified instances), and the whole directory compiles as part
of `dune build` / `make all` — the gallery cannot rot. Each file's header links to the theory file
where the *general* laws (∀-quantified, with frame clauses, mutants, and inhabitance) live.

| Effect | Ops | Demonstrates | Example | General theory |
|---|---|---|---|---|
| **Keyed store** (State) | `OGet` `OPut` `ODelete` | put/get round-trip, per-key frame, delete's answer | [`KeyedStore.v`](KeyedStore.v) | [`theories/KV.v`](../theories/KV.v), [`theories/TimeStore.v`](../theories/TimeStore.v) |
| **Expiry** | `OSetDeadline` `OGetDeadline` | TTLs; live iff `now ≤ deadline`, both boundary faces; PERSIST | [`Expiry.v`](Expiry.v) | [`theories/TimeStore.v`](../theories/TimeStore.v), [`theories/StoreAssert.v`](../theories/StoreAssert.v) |
| **Time** (Reader of the clock) | `ONow` | the injected instant; checked deadline arithmetic | [`Clock.v`](Clock.v) | [`theories/TimeStore.v`](../theories/TimeStore.v) |
| **Errors** | `OThrow` | short-circuit, committed pre-throw effects, structured payloads | [`Throw.v`](Throw.v) | [`theories/Error.v`](../theories/Error.v) |
| **Environment** (Reader) | `OAsk` | request/config dispatch; stability | [`Ask.v`](Ask.v) | [`theories/Env.v`](../theories/Env.v) |
| **Trace** (Writer) | `OTrace` | provable structured logging, in order | [`Tracing.v`](Tracing.v) | [`theories/Trace.v`](../theories/Trace.v) |
| **Cache** | `OCacheGet` `OCachePut` | memoization; the cache is invisible to the observable *by construction* | [`Memo.v`](Memo.v) | [`theories/Cache.v`](../theories/Cache.v) |
| **Journal** | `OJournal` | timestamped durability log; journaling never changes results (the frame law); replay | [`Journaling.v`](Journaling.v) | [`theories/Journal.v`](../theories/Journal.v) |
| **Files** | [`Files.v`](Files.v) | write-read roundtrip; exact counts at EOF chunk boundaries; modeled errors as values (`wc_prog_correct` / `chunking_invariance` in [`theories/FileIO.v`](../theories/FileIO.v)) |
| **Combinators** (not effects) | `Match` `Repeat` `Fold` + 16 checked prims | tagged-union dispatch, bounded loops, argv-style folds, soft-failing arithmetic/parsing | [`Combinators.v`](Combinators.v) | [`theories/Recur.v`](../theories/Recur.v), [`theories/Fold.v`](../theories/Fold.v), [`theories/Prims.v`](../theories/Prims.v) |

Beyond instances: the **program logic** (`theories/Logic.v`, a shallow weakest-precondition layer over
the same `run` — zero added trust) is what turns these into ∀-quantified specifications;
[`theories/LogicDemo.v`](../theories/LogicDemo.v) shows two end-to-end general theorems. The largest
consumer of all of this is **redoq**, a Redis-compatible server whose 22 data commands are EffIR
programs proven with exactly these tools.

To run one yourself: `dune build examples/` — or change an expected value and watch the proof fail,
which is the point.
