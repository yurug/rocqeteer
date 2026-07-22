---
id: effect-signatures
type: spec
summary: An effect signature is a type-indexed family of operations declared in Rocq, mirrored 1:1 by an OCaml extensible-effect declaration; KV is the slice-1 signature, and effects compose by explicit sum.
domain: spec
last-updated: 2026-07-10
depends-on: [effir]
refines: []
related: [reference-semantics, codegen, ext-ocaml5-effects]
---
# Spec — Effect signatures

## One-liner
An effect signature names a set of operations, each with fixed argument types and a fixed result type. The
result type being part of the operation is what makes typed codegen and typed OCaml handlers possible.

## Scope
How effects are declared in Rocq, how `Perform` references them, how the same signature maps to OCaml's
`type _ Effect.t += …`, and how multiple effects compose in v1. The KV signature is the slice-1 example.

## Rocq shape
A signature is a `Variant E : Type -> Type` whose constructors are the operations; the index is the result type.
```coq
Variant KV : Type -> Type :=
| Get    : key -> KV (option value)
| Put    : key -> value -> KV unit
| Delete : key -> KV unit.
```
In EffIR, an operation is referenced by `(effect_name, op_name)` with its declared arg `ty`s and result
`ty`; `Perform (KV,Get) [k]` is well-typed iff `k : TNamed "key"` and yields `TOption (TNamed "value")`.
See [[effir]].

## OCaml mirror (generated)
Each signature maps 1:1 to an extensible-variant extension plus thin `perform` wrappers:
```ocaml
type _ Effect.t +=
  | Get    : key -> value option Effect.t
  | Put    : key * value -> unit Effect.t
  | Delete : key -> unit Effect.t
(* val get : key -> value option = fun k -> Effect.perform (Get k)  (etc.) *)
```
Constructors are kept private behind the module signature; client/generated code calls `get`/`put`/`delete`,
not raw `Effect.perform` ([[ext-ocaml5-effects]], and the CI rule banning stray `perform`). The handler
that interprets them lives in `runtime/` and is placed at a stable region boundary ([[codegen]] §handlers).

## Operation result types (typed codegen hinge)
The result type in the constructor is authoritative end-to-end: it drives the EffIR typechecker, the OCaml
`Effect.t` index, and the handler's `continue kcont (v : result)` type. A mismatch is a type error in OCaml
(loud), not a runtime cast.

## Composing effects (v1)
v1 uses **explicit sums**, not a typeclass/row-polymorphic injection:
```coq
Variant SumE (E F : Type -> Type) : Type -> Type :=
| Inl : forall A, E A -> SumE E F A
| Inr : forall A, F A -> SumE E F A.
```
Verbose but transparent — the generator emits predictable constructors and the handler nesting order is
explicit. A typeclass-based `SubEff` injection is a possible later ergonomic layer, not v1.

## Slice-1 signature: KV
`Get`/`Put`/`Delete`. The KV signature stays parametric over `key`/`value`. **IR v2 milestone 1
(2026-07-10)**: the concrete instantiation is now `key = Z.t` and `value = Rval.t` (the native
OCaml sum mirroring `dval` in `theories/EffIR.v`; see `runtime/rval.ml`). Keys stay `Zarith.Z.t`;
bytes keys are a later milestone. The reference map is `FMapAVL` over `Z_as_OT`. Pure prims
`value_zero = Rval.Int Z.zero` / `value_succ = (fun (Rval.Int z) -> Rval.Int (Z.succ z))` are
emitted by the codegen and validated by `diff_kv` (registered, [[runtime-manifest]]). Abstract
`TNamed` key/value realization is deferred to the codec pilot (`plan.md` Resolution 3).

### Arity convention (codegen ↔ handler)
Effect constructors are **tupled** (`Put : key * value -> unit Effect.t`); the public `perform` wrappers are
**curried** (`put : key -> value -> unit`). Codegen lowers `Perform (KV,Put) [k;v]` through the curried
wrapper, so the generated `.mli`, the lowering, and the handler's `continue` types all agree.

## Agent notes
> Resist row-polymorphic/extensible-effect cleverness in v1 (the report warns against it too). Explicit
> sums keep the OCaml output reviewable and the handler order unambiguous — which is itself a trust property.

## Related files
- `spec/effir.md` — how `Perform`/`op` are typed inside terms.
- `external/ocaml5-effects.md` — one-shot continuations, deep handlers, `Effect.Unhandled`, `match…with effect`.
- `spec/reference-semantics.md` — the pure Rocq handler for KV used in proofs/tests.
</content>

## The file family (C3, adr-0017-file-io — added 2026-07-19)
| Op | Args | Result | Notes |
|----|------|--------|-------|
| `OOpen` | `[path : DBytes; mode : DInt 0 or 1]` | `DTag 0 (DInt fd)` or `DTag 1 (DInt 2)` (ENOENT value, read mode) | paths resolved ONLY here (inode pinning structural); mode 1 = write-truncate |
| `ORead` | `[fd : DInt; maxlen : DInt >= 1]` | `DBytes chunk` (EMPTY = EOF) or `DTag 1 (DInt 9)` (EBADF value) | deterministic chunk = `file_chunk` (firstn/skipn); `maxlen <= 0` is Dstuck |
| `OFWrite` | `[fd : DInt; bytes : DBytes]` | `DUnit` or `DTag 1 (DInt 9)` | appends; short writes do not exist at the IR level |
| `OClose` | `[fd : DInt]` | `DBool` | double-close = false (the ODelete shape) |

World regions: `files : M.t (list ascii)` (path -> contents), `fds : fdtab`, `next_fd : Z`.
Modeled failures are tagged VALUES; environmental failures live in the realizer
(`Rkv.Fileio`) behind the named assumptions `Runtime_FS_distinct_inodes` (runtime-checked),
`Runtime_FS_open_inode_stable` (detection), `Runtime_FileRead_full`/`Runtime_FileWrite_full`.
Flagship theorems: `FileIO.chunking_invariance`, `FileIO.wc_prog_correct`.

## The socket family (C4, adr-0018-sockets — added 2026-07-22)
| Op | Args | Result | Notes |
|----|------|--------|-------|
| `OAccept` | `[]` | `DTag 0 (DInt conn)` or `DTag 1 (DInt 11)` (script exhausted — EAGAIN value) | pops the injected connection script; ids from 1 |
| `ORecv` | `[conn : DInt; maxlen : DInt >= 1]` | `DBytes chunk` (EMPTY = the client's half-close) or `DTag 1 (DInt 9)` | `file_chunk` over the connection's scripted input |
| `OSend` | `[conn : DInt; bytes : DBytes]` | `DUnit` or `DTag 1 (DInt 9)` | appends to the connection's output |
| `OCloseConn` | `[conn : DInt]` | `DBool` | finalizes into the transcript `conn_log` — THE observable |

World regions: `conn_script`, `socks`, `conn_log`, `next_conn`. ONE-SHOT half-close-driven
connections (adr-0018 §1). Realizer `Rkv.Sockio` behind `Runtime_Sock_script_faithful`
(record-and-replay validated), `Runtime_SockRecv_full`/`Runtime_SockSend_full`, and the
receive-timeout liveness backstop. Flagship theorem: `SockIO.http_prog_correct`.
Rider prim (adr-0009 discipline): `PFindSub` — first-occurrence substring search.
