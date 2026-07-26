---
title: "Pragmatic Effectful Extraction from Rocq to Idiomatic OCaml"
subtitle: "A Lean-style architecture for certified, performant, effectful programs"
author: "OpenAI GPT-5.5 Pro"
date: "2026-06-20"
lang: en-US
---

# Pragmatic Effectful Extraction from Rocq to Idiomatic OCaml

**Audience.** This report is written for an engineering team or a code agent that will prototype a pragmatic extraction pipeline from Rocq/Coq programs to idiomatic OCaml 5 code.

**Status.** Design proposal. Some components are immediately implementable. Some components, especially proof-producing code generation for OCaml effect handlers, are research-grade and should be introduced incrementally.

**Core thesis.** Rocq should own the algebra, specifications, laws, proofs, and reference semantics. OCaml should own the runtime representations, direct-style execution, native mutation, GADTs, and effect handlers. The trust boundary must be explicit, narrow, auditable, and tested aggressively.

## Contents

1. Executive summary
2. Goals and non-goals
3. Baseline facts and constraints
4. Proposed architecture
5. Rocq programming model for effects
6. OCaml runtime model
7. Code generation strategy
8. Native realizers and data representations
9. GADTs as typed runtime witnesses
10. Reasoning discipline
11. TCB model
12. Testing, fuzzing, and CI
13. Performance engineering
14. Repository layout
15. Implementation roadmap
16. Detailed tasks for a code agent
17. Worked example: key-value state effect
18. Worked example: typed protocol encoding
19. Risks and mitigations
20. References

# 1. Executive summary

The current Rocq extraction mechanism is a safe and useful baseline, but it is not a performance-oriented compiler. It erases logical content and prints relatively direct ML code. It can map Rocq constants and inductive types to OCaml code, but those mappings are copied as user-provided strings and are not checked by Rocq. The manual explicitly states that `Extract Constant` code is copied into generated files and that it is the user's responsibility to ensure the ML term has the expected type [R1]. Rocq also inserts `Obj.magic` in some cases where the Rocq and ML type systems diverge, and it does not yet generate GADTs for those cases [R1]. Primitive integers, floats, arrays, and strings exist in Rocq, but their OCaml runtime modules must still be supplied by the user [R2].

The proposed solution is not to make standard extraction magically optimize everything. Instead, build a **Rocq Native Runtime and Effectful Code Generator**:

```text
Rocq specs, laws, reference handlers, proofs
        |
        |  recognized effectful DSL or quoted monadic program
        v
Effect IR with typed operations and explicit handlers
        |
        |  trusted small code generator
        v
Idiomatic OCaml 5 direct style
        |
        |  native effects, refs, arrays, bytes, GADTs, Hashtbl, Eio/Unix
        v
Fast executable plus extracted reference model plus differential tests
```

This is a Lean-style design: keep the proof kernel conservative, but allow the compiler/runtime path to use trusted native code under a clear discipline. Lean itself separates the compiler-facing pre-definition from the kernel-facing logical translation, and allows the compiler to compile partial or unsafe functions that the kernel treats differently or does not accept [R12]. We should copy the engineering idea, not the exact implementation.

The key design rule is:

> Reason about algebraic effects in Rocq. Execute them in OCaml direct style. Do not execute free monads or interaction trees on hot paths.

The MVP should support five families of effects:

1. `State`: local state, mutable arrays, bytes, counters, caches.
2. `Error`: exceptions or result-like failures.
3. `Env`: read-only context, protocol constants, configuration.
4. `Trace/IO`: abstract event traces and controlled I/O boundaries.
5. `Cache/Oracle`: memoization, hash-consing, external callbacks.

Avoid multi-shot continuations in the initial design. OCaml 5 continuations are one-shot; resuming a continuation more than once raises `Continuation_already_resumed`, and OCaml does not statically check effect safety or ensure every continuation is resumed at least once [R6]. This is a feature for systems programming and concurrency, but it must shape the source DSL.

# 2. Goals and non-goals

## Goals

**G1. Program with effects in Rocq.** Provide a usable Rocq-level interface for effectful programs: state, error, environment, traces, caches, and selected I/O abstractions.

**G2. Reason in Rocq.** Provide pure reference semantics and proof principles: algebraic laws, Hoare/Dijkstra-style specifications, refinement against abstract handlers, and executable reference handlers.

**G3. Generate idiomatic OCaml.** Compile recognized effectful programs to direct-style OCaml 5 using `perform`, deep handlers, exceptions, local mutation, arrays, bytes, and GADTs.

**G4. Keep the TCB explicit.** Accept a larger TCB than fully verified extraction, but make it small, stable, named, reviewed, and measurable.

**G5. Preserve engineering ergonomics.** Generated OCaml should look like good OCaml, not a dump of a free monad interpreter. It should interact with existing OCaml libraries and be inspectable by OCaml engineers.

**G6. Support performance work.** The design must expose enough control to optimize allocation, boxing, array access, bytes, exceptions, and handler placement.

## Non-goals

**NG1. Do not compile arbitrary Gallina to optimal OCaml in v1.** The first prototype should handle a restricted, recognized effectful fragment. General Gallina lowering can come later.

**NG2. Do not prove the whole OCaml runtime.** The design assumes the OCaml compiler and runtime, including effect handlers, are part of the executable TCB.

**NG3. Do not use OCaml effects for multi-shot nondeterminism initially.** Nondeterminism, search, and backtracking should be compiled to explicit lists, streams, or search structures, not by duplicating captured continuations.

**NG4. Do not hide `Extract Constant`.** Custom extraction remains useful, but it must go through a manifest, a reviewed runtime module, and generated tests.

**NG5. Do not expose arbitrary `Obj.magic`.** Any unavoidable cast must be isolated behind a generated or handwritten GADT witness module with a very small public surface.

# 3. Baseline facts and constraints

## 3.1 Standard Rocq extraction is useful but weakly optimized

Rocq extraction targets OCaml, Haskell, and Scheme. It is meant to build certified and relatively efficient functional programs from Rocq functions or constructive proofs [R1]. It performs erasure and some simplifications. It has inlining options and a few special cases, but it is not a full optimizing compiler.

Two consequences matter:

1. The extracted shape often follows proof-oriented Gallina definitions rather than runtime-oriented OCaml definitions.
2. Mapping a Rocq representation to a native OCaml representation does not automatically improve the algorithms that manipulate it.

The manual gives the classic warning: extracting `nat` to OCaml `int` does not change the asymptotic complexity of functions such as `Nat.mul`; one needs corresponding primitive implementations if available [R1]. The historical `ExtrOcamlNatInt` module also labels its efficient `nat` realizers as uncertified and suitable mainly for testing/prototyping [R3].

## 3.2 Custom realizers are powerful and dangerous

`Extract Constant`, `Extract Inlined Constant`, `Extract Inductive`, and `Extract Foreign Constant` allow Rocq constants, inductives, and foreign calls to be mapped to ML code. This is the right hook for performance, but the documentation states that the ML code is not checked by extraction and is copied as a string [R1].

This proposal keeps those hooks, but replaces informal string snippets with a disciplined runtime manifest:

```text
Rocq constant        Runtime module      OCaml symbol      Contract      Tests
Runtime.Bytes.get    Runtime_bytes       get_u8            get_spec      yes
Runtime.KV.get       Runtime_kv          perform_get       get_law       yes
Runtime.Int63.add    Runtime_int63       add               modulo_spec   yes
```

## 3.3 Rocq primitives already point toward a native runtime

Rocq has primitive integers, floats, persistent arrays, and byte strings. Their declarations are regular axioms, and their extraction to OCaml can be customized. Rocq provides modules such as `ExtrOCamlInt63`, `ExtrOCamlFloats`, `ExtrOCamlPArray`, and `ExtrOCamlPString`, but the corresponding OCaml modules are not produced by extraction and must be supplied by the user [R2].

This is exactly the shape we want: trusted primitives with explicit runtime implementations. The proposal generalizes this pattern to effects, bytes, mutable arrays, hash tables, caches, typed encodings, and external I/O.

## 3.4 OCaml 5 effects are efficient but dynamically checked

OCaml 5 effect handlers are user-defined effects with handlers around computations. They generalize exceptions and enable non-local control flow such as resumable exceptions, lightweight threads, coroutines, generators, and asynchronous I/O [R6]. An effect constructor extends the extensible GADT `Effect.t`:

```ocaml
type _ Effect.t += Xchg : int -> int Effect.t
```

The implementation uses runtime-managed fibers. Capturing and resuming continuations does not copy stack frames, which is why effect suspension and resumption can be efficient [R6].

Important constraints:

- OCaml does not statically check that all effects are handled; an unhandled effect raises `Effect.Unhandled` [R6].
- Continuations are one-shot; resuming a continuation more than once raises `Continuation_already_resumed` [R6].
- OCaml does not ensure a captured continuation is resumed at least once; leaks or resource retention are possible [R6].
- Effects cannot cross some C-to-OCaml callback boundaries [R6].

The source DSL and generated runtime must respect these constraints.

## 3.5 ITrees and FreeSpec are good semantic bases

Interaction Trees are a Coq data structure for representing recursive and impure computations that interact with an environment. They are a coinductive variant of free monads built from uninterpreted events and continuations. They support interpreters from event handlers and have a rich equational theory up to weak bisimulation [R10].

FreeSpec models components as programs with algebraic effects realized by other components. It was designed for modular modeling and verification of complex systems in Coq [R11].

The proposed design can use ITree as the canonical semantic model and borrow FreeSpec's component discipline. For code generation, however, we should not execute ITree/free structures in hot paths.

## 3.6 MetaRocq/Malfunction is the longer-term verified path

The MetaRocq verified extraction project targets Malfunction, a specification of Lambda, the internal language of the OCaml compiler. Its README states that the implementation supports Rocq constructs including primitive integers, floats, and arrays, while the cofixpoint to lazy/force translations are not verified yet [R4]. The associated paper describes a verified extraction pipeline to OCaml/Malfunction and discusses safe interoperability with unverified code [R5].

This proposal is compatible with MetaRocq/Malfunction, but does not require it for the MVP. The pragmatic path starts with a small trusted effect code generator and runtime manifest. A later phase can replace parts of the generator with verified MetaRocq passes.

# 4. Proposed architecture

## 4.1 High-level pipeline

```text
+---------------------------------------------------------------+
| Rocq source                                                   |
| - pure specs                                                  |
| - effect signatures                                           |
| - effectful programs in DSL or recognized monadic form         |
| - reference handlers                                           |
| - algebraic laws and Hoare/Dijkstra specs                      |
+---------------------------+-----------------------------------+
                            |
                            v
+---------------------------------------------------------------+
| Effect IR                                                     |
| - typed operations                                            |
| - return types                                                |
| - binds, lets, matches, fixpoints                             |
| - handler boundaries                                          |
| - native realizer references                                  |
+---------------------------+-----------------------------------+
                            |
               +------------+------------+
               |                         |
               v                         v
+-----------------------------+    +-----------------------------+
| Reference extraction         |    | Fast OCaml codegen          |
| - ITree/free interpreter     |    | - direct style              |
| - slow but simple            |    | - perform/handlers          |
| - oracle for tests           |    | - native runtime modules    |
+-----------------------------+    +-----------------------------+
               |                         |
               +------------+------------+
                            v
+---------------------------------------------------------------+
| Validation                                                     |
| - Rocq proofs against reference semantics                      |
| - differential tests: reference vs fast                        |
| - fuzz/property/metamorphic tests                              |
| - TCB manifest and assumption report                           |
| - benchmarks and allocation profiles                           |
+---------------------------------------------------------------+
```

## 4.2 Trust boundaries

There are two semantic artifacts:

1. **Reference semantics.** A pure Rocq interpreter for effects. This is the basis for proofs.
2. **Fast semantics.** OCaml 5 handlers and native data structures. This is the implementation path.

The bridge between them is a runtime contract:

```coq
Axiom Runtime_KV_refines :
  forall p s,
    observable (run_fast_KV p s) = run_spec_KV p s.
```

This axiom is not hidden. It is listed in the TCB manifest, tied to an OCaml module, and supported by differential tests.

## 4.3 Two implementation modes

### Mode A: Deep DSL first

A typed deep embedding in Rocq:

```coq
Inductive Eff (E : Type -> Type) : Type -> Type :=
| Ret     : forall A, A -> Eff E A
| Bind    : forall A B, Eff E A -> (A -> Eff E B) -> Eff E B
| Trigger : forall A, E A -> Eff E A
| Match   : ...
| Fix     : ... .
```

Pros:

- Very simple to interpret and code-generate.
- Clear effect operations and handler boundaries.
- Good for a first code agent.

Cons:

- Less ergonomic than direct Gallina.
- Harder to reuse arbitrary Rocq functions.

### Mode B: Recognized monadic Gallina later

Allow users to write:

```coq
Definition incr (k : key) : M unit :=
  x <- get k;;
  put k (S x).
```

Then use MetaRocq or a custom plugin to quote the definition and lower recognized monadic structure to `EffIR`.

Pros:

- Much better ergonomics.
- Closer to normal Rocq development.

Cons:

- More complex code generator.
- More opportunities for unsupported Gallina constructs.

**Recommendation.** Implement Mode A first. Add Mode B only after the runtime, tests, and CI discipline are stable.

# 5. Rocq programming model for effects

## 5.1 Effect signatures

An effect signature is a type-indexed family of operations:

```coq
Variant KV : Type -> Type :=
| Get    : key -> KV (option value)
| Put    : key -> value -> KV unit
| Delete : key -> KV unit.
```

This shape mirrors OCaml's `Effect.t` extension:

```ocaml
type _ Effect.t +=
  | KV_get    : key -> value option Effect.t
  | KV_put    : key * value -> unit Effect.t
  | KV_delete : key -> unit Effect.t
```

The return type of the operation is part of the constructor type. This is the key to typed effect code generation.

## 5.2 Composing effects

For the MVP, use explicit sums:

```coq
Variant SumE (E F : Type -> Type) : Type -> Type :=
| Inl : forall A, E A -> SumE E F A
| Inr : forall A, F A -> SumE E F A.
```

This is verbose but transparent. Later, provide typeclass-based injection:

```coq
Class SubEff (E F : Type -> Type) :=
  inj : forall A, E A -> F A.
```

Avoid clever overlapping effect machinery in v1. The generator should produce explicit, predictable OCaml constructors.

## 5.3 Computation type

Use an ITree-compatible core:

```coq
Definition M (E : Type -> Type) (A : Type) := itree E A.
```

or a simpler finite free monad for terminating first-order kernels:

```coq
Inductive Prog (E : Type -> Type) (A : Type) :=
| Ret : A -> Prog E A
| Op  : forall X, E X -> (X -> Prog E A) -> Prog E A.
```

**Recommendation.** Use a simple `Prog` for the first generator. Provide an interpretation into ITree when nontermination or coinductive reasoning is needed.

Why not start with full ITree codegen? Because codegen from coinductive structures plus guarded recursion is more complex. A finite `Prog` covers many hot kernels: encoders, decoders, state transformations, caches, local mutable algorithms, and checked I/O fragments.

## 5.4 Surface syntax

Expose a notation layer:

```coq
Notation "x <- p ;; q" := (bind p (fun x => q))
  (at level 100, p at next level, right associativity).

Notation "p ;; q" := (bind p (fun _ => q))
  (at level 100, right associativity).

Definition get (k : key) : Prog KV (option value) :=
  trigger (Get k).

Definition put (k : key) (v : value) : Prog KV unit :=
  trigger (Put k v).
```

Users write:

```coq
Definition incr (k : key) : Prog KV unit :=
  ox <- get k;;
  match ox with
  | None => put k 1
  | Some x => put k (x + 1)
  end.
```

## 5.5 Reference handlers

A handler gives pure semantics to an effect signature:

```coq
Definition kv_state := FMap.t value.

Definition handle_kv {A}
  (op : KV A)
  (s : kv_state)
  : A * kv_state :=
  match op with
  | Get k => (FMap.find k s, s)
  | Put k v => (tt, FMap.add k v s)
  | Delete k => (tt, FMap.remove k s)
  end.
```

Then interpret programs:

```coq
Fixpoint run_kv {A} (p : Prog KV A) (s : kv_state)
  : A * kv_state :=
  match p with
  | Ret x => (x, s)
  | Op _ op k =>
      let '(x, s') := handle_kv op s in
      run_kv (k x) s'
  end.
```

This interpreter is the proof target and test oracle.

## 5.6 Algebraic laws

Each effect family should declare laws. For state:

```coq
get k ;; get k = get k
put k v ;; get k = put k v ;; ret (Some v)
put k v1 ;; put k v2 = put k v2
```

For error:

```coq
throw e >>= k = throw e
catch (ret x) h = ret x
catch (throw e) h = h e
```

For environment:

```coq
ask >>= fun r => ask = ask
local f (ask) = fmap f ask
```

These laws should be proven for the reference handlers. The OCaml runtime handlers are assumed to refine them and validated by tests.

## 5.7 Dijkstra/Hoare layer

For serious code, raw equivalence proofs become noisy. Add a Hoare or Dijkstra layer:

```coq
Record Spec (S A : Type) := {
  pre  : S -> Prop;
  post : S -> A -> S -> Prop;
}.

Definition verifies {A}
  (p : Prog KV A)
  (spec : Spec kv_state A) : Prop :=
  forall s, pre spec s ->
    let '(x, s') := run_kv p s in
    post spec s x s'.
```

For example:

```coq
Theorem incr_spec :
  verifies (incr k)
    {| pre := fun _ => True;
       post := fun s _ s' =>
         FMap.find k s' = Some (1 + default 0 (FMap.find k s)) |}.
```

The generated OCaml does not carry this proof. It is linked to it through the runtime refinement axiom and tests.

# 6. OCaml runtime model

## 6.1 Effect declarations

For every Rocq effect signature, generate or write an OCaml module:

```ocaml
module KV_effect : sig
  type key
  type value

  type _ Effect.t +=
    | Get : key -> value option Effect.t
    | Put : key * value -> unit Effect.t
    | Delete : key -> unit Effect.t

  val get : key -> value option
  val put : key -> value -> unit
  val delete : key -> unit
end = struct
  type key = Runtime_key.t
  type value = Runtime_value.t

  type _ Effect.t +=
    | Get : key -> value option Effect.t
    | Put : key * value -> unit Effect.t
    | Delete : key -> unit Effect.t

  let get k = Effect.perform (Get k)
  let put k v = Effect.perform (Put (k, v))
  let delete k = Effect.perform (Delete k)
end
```

Keep the constructors private if possible through module signatures. Client code should call `get`, `put`, and `delete`, not construct raw effects unless generated.

## 6.2 Direct-style generated code

Rocq:

```coq
Definition incr (k : key) : Prog KV unit :=
  ox <- get k;;
  match ox with
  | None => put k 1
  | Some x => put k (x + 1)
  end.
```

Generated OCaml:

```ocaml
let incr k =
  match KV_effect.get k with
  | None -> KV_effect.put k 1
  | Some x -> KV_effect.put k (x + 1)
```

No monadic allocation remains. No `Bind` constructors remain. No free monad interpreter runs in production.

## 6.3 Deep handlers for first-order effects

A handler for a mutable hash table:

```ocaml
open Effect.Deep

let run_kv (table : (Key.t, Value.t) Hashtbl.t) (f : unit -> 'a) : 'a =
  try f () with
  | effect (KV_effect.Get k), kcont ->
      continue kcont (Hashtbl.find_opt table k)
  | effect (KV_effect.Put (k, v)), kcont ->
      Hashtbl.replace table k v;
      continue kcont ()
  | effect (KV_effect.Delete k), kcont ->
      Hashtbl.remove table k;
      continue kcont ()
```

This is idiomatic OCaml 5. Deep handlers reinstall themselves across `continue`, which is exactly what first-order operations need [R6].

## 6.4 Handler placement rule

Do not wrap every tiny function in a handler. Effects should be handled at stable region boundaries:

```ocaml
let run_transaction env input =
  Runtime_error.run @@ fun () ->
  Runtime_trace.run env.trace @@ fun () ->
  Runtime_kv.run env.table @@ fun () ->
  Generated.Protocol.apply input
```

Handler nesting is a performance and semantics decision. The generator should not guess. The entrypoint manifest declares required handlers and their order.

## 6.5 Effect safety wrapper

OCaml lacks static effect safety. Every exported entrypoint should be generated as a closed runner:

```ocaml
let apply_checked env input =
  try Ok (run_transaction env input) with
  | Effect.Unhandled eff ->
      Error (`Unhandled_effect (Runtime_effect_name.describe eff))
  | Runtime_error.E e ->
      Error (`Runtime_error e)
  | exn ->
      Error (`Unexpected_exception exn)
```

In production, one might not catch all exceptions at deep internal levels, but generated public APIs should never leak unhandled effects accidentally.

## 6.6 State regions

For local mutation, use an ST-like region discipline in Rocq:

```coq
Parameter ST : Type -> Type -> Type.
Parameter runST : (forall s, ST s A) -> A.
```

Runtime extraction:

```ocaml
let run_st f = f ()
```

Inside the region, generated OCaml can use refs, arrays, bytes, and mutable records. Outside the region, the interface remains pure.

This is one of the highest-value native realizers because many algorithms need local mutation but should expose pure semantics.

## 6.7 Error effects

Two possible backends:

1. `Result` backend for explicit APIs.
2. Exception backend for direct-style performance.

Rocq model:

```coq
Variant ErrorE (E : Type) : Type -> Type :=
| Throw : E -> ErrorE E Empty_set.
```

OCaml direct style:

```ocaml
exception Runtime_error of Error.t

let throw e = raise (Runtime_error e)
let run_error f =
  try Ok (f ()) with Runtime_error e -> Error e
```

Rule: exceptions are allowed only as a backend for a typed Rocq `ErrorE` effect or for local control. No arbitrary exceptions in generated code.

## 6.8 Trace and I/O effects

Rocq should reason about I/O through traces or abstract environments:

```coq
Variant IOE : Type -> Type :=
| Read_file  : path -> IOE (result bytes io_error)
| Write_file : path -> bytes -> IOE (result unit io_error)
| Now        : IOE timestamp.
```

The reference handler consumes an abstract environment and produces a trace. The OCaml handler calls Unix, Eio, or project-specific services.

Do not model all Unix behavior initially. Provide a finite set of stable operations needed by the target project.

# 7. Code generation strategy

## 7.1 Codegen principle

Compile effectful syntax by erasing the monadic structure:

```text
Rocq                     OCaml
----                     -----
ret x                    x
x <- p ;; q              let x = compile(p) in compile(q)
trigger (Op args)        Runtime.Op.perform args
match p with ...         match compile(p) with ...
handler h p              try compile(p) with effect ...
```

The generator should not emit a generic interpreter for production. It should emit direct-style OCaml.

## 7.2 Effect IR

Define a typed IR that is smaller than Gallina and easier to print:

```ocaml
type ty =
  | TUnit
  | TInt63
  | TBool
  | TOption of ty
  | TPair of ty * ty
  | TNamed of string
  | TArrow of ty * ty

type op = {
  effect_name : string;
  constructor : string;
  args : ty list;
  ret : ty;
}

type expr =
  | Var of string
  | Let of string * expr * expr
  | Ret of expr
  | Perform of op * expr list
  | Match of expr * branch list
  | Call of string * expr list
  | Lambda of string * ty * expr
  | App of expr * expr
  | Fix of fix_decl
  | Native of native_ref * expr list
```

The generator consumes `expr`, not arbitrary Coq terms.

## 7.3 Lowering options

### Option 1: Deep embedding printer

Rocq definitions are terms of `Prog E A`. Write a Rocq or OCaml tool that traverses the deep syntax and prints JSON:

```json
{
  "kind": "let",
  "name": "ox",
  "rhs": { "kind": "perform", "effect": "KV", "op": "Get", "args": ["k"] },
  "body": { "kind": "match", "scrutinee": "ox", "branches": [...] }
}
```

This is the fastest route for a code agent.

### Option 2: MetaRocq recognizer

Use MetaRocq to quote Gallina and recognize the monadic pattern:

```coq
bind (trigger (Get k)) (fun ox => ...)
```

This gives better source ergonomics but takes more effort.

### Option 3: Standard extraction plus rewriting

Extract a reference program, then rewrite the OCaml AST. This is tempting but fragile. It couples the generator to Rocq's printed OCaml and should be avoided.

**Recommendation.** Start with Option 1, then add Option 2.

## 7.4 Codegen decisions

The generator must be deterministic and reviewable. It should output:

```text
_generated/
  protocol_generated.ml
  protocol_generated.mli
  protocol_effects.ml
  protocol_effects.mli
  protocol_handlers.ml
  protocol_handlers.mli
  runtime_manifest.json
  tcb_report.md
```

Each generated file should contain a header:

```ocaml
(* Generated by rocq-eff-codegen.
   Source: theories/Protocol/Apply.v
   Effect manifest hash: sha256:...
   Runtime contract hash: sha256:...
   Do not edit manually. *)
```

## 7.5 Unsupported constructs

The generator should fail loudly on unsupported features:

- impredicative data that would need arbitrary casts;
- dependent matches that do not erase to a supported GADT witness;
- higher-order effect operations not declared as safe;
- multi-shot continuations;
- cofixpoints in v1;
- recursion without an approved extraction strategy;
- calls to unregistered native primitives.

A failed codegen is better than a clever unsound codegen.

## 7.6 Recursion

For v1, support:

1. structurally recursive functions over lists/trees;
2. bounded loops over native `int` ranges;
3. tail-recursive loops;
4. well-founded recursion only if an explicit fuel or measure is compiled.

Rocq proof-oriented recursion often uses recursors whose runtime shape is poor. A Lean-style path should compile the source-level recursion when safe rather than the kernel-level recursor translation. This is the same motivation Lean documents: the compiler receives recursive pre-definitions as-is, while the kernel receives a logical transformation [R12].

For the MVP, declare loops explicitly:

```coq
for_i : int -> int -> (int -> ST s unit) -> ST s unit
```

Generate:

```ocaml
for i = lo to hi - 1 do
  body i
 done
```

This is a deliberate trusted realizer, not standard extraction.

# 8. Native realizers and data representations

## 8.1 Realizer concept

A realizer maps a Rocq-level abstract type or operation to an OCaml implementation:

```coq
Record RealizerSpec := {
  coq_name      : string;
  ocaml_module  : string;
  ocaml_symbol  : string;
  purity        : Purity;
  precondition  : Prop;
  postcondition : Prop;
}.
```

In practice, the manifest should be machine-readable:

```toml
[primitive."Runtime.Bytes.get_u8"]
ocaml_symbol = "Rocq_runtime.Bytes.get_u8"
purity = "pure"
raises = []
pre = "0 <= i < length b"
post = "returns byte at i"
tests = ["bytes_get_matches_reference"]
```

## 8.2 Realizer classes

### Pure native value realizers

Examples:

- `Uint63.int` to OCaml `int` or project-specific `Int63.t`.
- `bytes` to OCaml `bytes` or `string` depending on mutability.
- `timestamp` to `int64` or project-specific type.

### Local mutable realizers

Examples:

- arrays inside `runST`;
- bytes builders;
- buffers;
- memo tables;
- hash-consing tables.

### Effect realizers

Examples:

- `ErrorE` to exceptions;
- `TraceE` to a buffer or event sink;
- `IOE` to Eio/Unix/project services;
- `CacheE` to `Hashtbl`.

### Typed witness realizers

Examples:

- protocol type witnesses;
- typed encodings;
- Michelson-like typed stacks;
- GADT equality proofs.

## 8.3 Suggested initial runtime modules

```text
runtime/
  Runtime_int63.mli/ml
  Runtime_bytes.mli/ml
  Runtime_buffer.mli/ml
  Runtime_array_region.mli/ml
  Runtime_error.mli/ml
  Runtime_trace.mli/ml
  Runtime_cache.mli/ml
  Runtime_effect_safety.mli/ml
  Runtime_gadt_witness.mli/ml
```

Each module must have:

- a Rocq spec file;
- an OCaml `.mli` file;
- an implementation `.ml` file;
- unit tests;
- property tests against a reference implementation;
- a manifest entry;
- an owner.

## 8.4 Arrays

Rocq primitive arrays are persistent arrays. Operationally, their implementation keeps one version as an OCaml native array and other versions as lists of modifications; access can become `O(n)` for versions where many cells are modified [R2]. This is good for proof-side computation, but not necessarily for hot runtime paths.

For hot paths, use two abstractions:

1. `PArray` for persistent semantics when sharing matters.
2. `MArray s A` inside `ST s` for local mutation.

Rocq spec:

```coq
Parameter MArray : Type -> Type -> Type.
Parameter new    : nat -> A -> ST s (MArray s A).
Parameter get    : MArray s A -> int -> ST s A.
Parameter set    : MArray s A -> int -> A -> ST s unit.
Parameter freeze : MArray s A -> ST s (list A).
```

OCaml:

```ocaml
type 'a marray = 'a array
let new_array n x = Array.make n x
let get a i = Array.unsafe_get a i   (* only if bounds proven or checked upstream *)
let set a i x = Array.unsafe_set a i x
```

Unsafe array access should be a separate realizer requiring a bound proof or dynamic debug checks.

## 8.5 Bytes and buffers

OCaml `Bytes` is a mutable fixed-length byte sequence with constant-time indexing and in-place modification [R9]. This is ideal for parsers and encoders.

Expose two Rocq abstractions:

```coq
Parameter bytes : Type.       (* immutable byte string *)
Parameter builder : Type.     (* mutable region-local builder *)
```

Runtime options:

- `bytes` maps to OCaml `string` for immutable data or `bytes` for copied data.
- `builder` maps to `Buffer.t` or `Bytes.t` inside a region.

Use explicit conversions:

```coq
freeze_builder : builder s -> ST s bytes
```

No aliasing of mutable `bytes` should escape the region unless the API guarantees no further mutation.

## 8.6 Integers

Use a small number of integer classes:

```text
uint63   modulo arithmetic, maps to Rocq Uint63 or OCaml int with platform discipline
int64    protocol-level fixed width, maps to int64
z        unbounded, maps to Zarith when needed
nat      proof/fuel only, not hot runtime arithmetic
```

Do not globally remap `nat` to `int`. Use explicit bounded integer types for runtime values.

## 8.7 Hash tables and maps

For proofs, use finite maps with extensional semantics. For runtime, use:

- `Map` for deterministic ordered maps;
- `Hashtbl` for caches and memoization;
- project-specific hash tables where stable hashing matters.

A cache effect should usually be observationally invisible except for performance:

```coq
cache_get : key -> M (option value)
cache_put : key -> value -> M unit
```

The spec can model cache misses conservatively. Runtime can be more aggressive.

# 9. GADTs as typed runtime witnesses

## 9.1 Why GADTs matter

OCaml GADTs allow constructors to refine type parameters and to hide existential variables. The OCaml manual describes them as extending variants with constructor-specific constraints and existential type variables [R7].

Rocq extraction sometimes inserts `Obj.magic` when Rocq terms are not directly typable in ML; the manual notes that GADTs are not yet produced by extraction for one such case [R1]. For a pragmatic runtime, we should manually generate or write GADT witness modules instead of letting casts spread.

## 9.2 Runtime type witnesses

Example:

```ocaml
type _ ty =
  | Unit  : unit ty
  | Bool  : bool ty
  | Int   : int ty
  | Bytes : bytes ty
  | Pair  : 'a ty * 'b ty -> ('a * 'b) ty
  | Option : 'a ty -> 'a option ty
```

Equality witness:

```ocaml
type (_, _) eq = Refl : ('a, 'a) eq

val eq_ty : 'a ty -> 'b ty -> ('a, 'b) eq option
```

This module is allowed to contain a tiny, reviewed use of `Obj.magic` only if the structural equality proof cannot otherwise convince OCaml. Prefer fully typed implementations.

## 9.3 Typed protocol encodings

For a protocol encoding layer:

```ocaml
type _ encoding =
  | Int64 : int64 encoding
  | Bytes : bytes encoding
  | Pair  : 'a encoding * 'b encoding -> ('a * 'b) encoding
  | List  : 'a encoding -> 'a list encoding

val encode : 'a encoding -> 'a -> bytes
val decode : 'a encoding -> bytes -> ('a, error) result
```

Rocq sees an abstract family:

```coq
Parameter encoding : Type -> Type.
Parameter encode : encoding A -> A -> bytes.
Parameter decode : encoding A -> bytes -> result A error.
Axiom decode_encode : forall A (e : encoding A) x,
  decode e (encode e x) = Ok x.
```

The OCaml GADT enforces the index at runtime. The proof of `decode_encode` is either established for a Rocq reference model or accepted as a runtime axiom for the native implementation.

## 9.4 Michelson/Octez relevance

Octez documentation explicitly says GADTs are widely used in the codebase, especially in the protocol, and that they increase type safety of the Michelson interpreter [R15]. This proposal should align with that style rather than fight it. Rocq can specify the typing relation; OCaml GADTs can enforce it in the runtime representation.

# 10. Reasoning discipline

## 10.1 Three levels of reasoning

### Level 1: Algebraic laws

Prove local equations:

```coq
put k v ;; get k = put k v ;; ret (Some v)
throw e >>= k = throw e
ask >>= fun r => ask = ask
```

These laws drive rewrites and simplification.

### Level 2: Handler refinement

Prove that a pure handler implements an abstract specification:

```coq
Theorem kv_handler_refines_map_model :
  forall p s,
    run_kv p s = map_model p s.
```

This is entirely in Rocq.

### Level 3: Runtime refinement assumption

Assume and test:

```coq
Axiom ocaml_kv_refines_kv_handler :
  forall p s,
    observe_ocaml (run_kv_fast p s) = run_kv p s.
```

This axiom is part of the executable TCB.

## 10.2 Reference/fast dual implementation

Every effectful entrypoint has two implementations:

```text
reference: extracted Rocq interpreter over Prog/ITree
fast:      generated OCaml direct style with native handlers
```

CI checks:

```text
for all generated test inputs:
  normalize(reference(input)) = normalize(fast(input))
```

Normalization handles benign differences such as trace timestamps, exception wrappers, or map ordering.

## 10.3 Proof style recommendations

Use Rocq proofs for:

- functional correctness of algorithms under reference handlers;
- invariant preservation;
- serialization round trips in the reference model;
- algebraic laws;
- bounds that justify unsafe runtime access;
- absence of impossible cases in typed protocol code.

Use runtime contracts/tests for:

- OCaml handler correspondence;
- native bytes/buffer behavior;
- hash table cache behavior;
- exception mapping;
- interaction with Unix/Eio/project services;
- performance invariants.

## 10.4 Avoiding proof/runtime divergence

The main risk is that the Rocq program being proved is not the program being run. Mitigate with:

- generated code from the same `EffIR` as the reference interpreter;
- no hand-edited generated files;
- manifest hashes in generated headers;
- differential tests at every public entrypoint;
- `Print Assumptions` reports committed to CI;
- runtime contract files reviewed like API changes.

# 11. TCB model

## 11.1 TCB layers

### Proof TCB

For theorem validity:

```text
Rocq kernel
Rocq axioms explicitly imported
plugins/tactics used to construct proofs
logical assumptions in specs
```

Keep this conservative.

### Extraction/runtime TCB

For executable correctness relative to the reference semantics:

```text
standard extraction for reference model
rocq-eff-codegen
OCaml compiler and runtime
OCaml effect handler semantics
Runtime_* modules
runtime manifest correctness
native dependency behavior
```

### System TCB

For deployment:

```text
OS, filesystem, network, clock, C stubs, cryptographic libraries,
build system, package manager, hardware, deployment configuration
```

## 11.2 TCB budget

Set hard engineering budgets:

```text
effect code generator core:      <= 3,000 LOC
runtime core excluding libraries: <= 2,000 LOC
each primitive module:           <= 500 LOC unless separately reviewed
Obj.magic uses:                  0 by default, <= 1 tiny witness module if justified
C stubs:                         0 in MVP
unchecked Extract Constant:       0
```

This is not a formal guarantee. It is an engineering control.

## 11.3 Unsafe policy

```text
Allowed:
- local mutation behind ST-like interfaces
- exceptions as backend for ErrorE
- OCaml effects behind generated handlers
- unsafe array/bytes access only with proof or debug check
- GADTs for typed witnesses

Forbidden by default:
- arbitrary Obj.magic
- Marshal for trusted data
- C stubs crossing effectful callbacks
- unregistered Extract Constant snippets
- unhandled effects escaping public APIs
- multi-shot continuation emulation via repeated continue
```

## 11.4 TCB report generated by CI

Each build should generate:

```text
tcb_report.md
  - Rocq version
  - OCaml version
  - codegen version and hash
  - runtime manifest hash
  - list of Extract Constant / Extract Inductive / Extract Foreign Constant
  - list of Rocq axioms from Print Assumptions
  - list of Obj.magic occurrences
  - list of external C stubs
  - list of public effectful entrypoints and handlers
  - test and benchmark summary
```

Build failure conditions:

- unregistered primitive;
- new axiom without review label;
- `Obj.magic` outside approved module;
- `Effect.perform` outside generated/runtime modules;
- generated file modified manually;
- missing differential tests for a public entrypoint.

# 12. Testing, fuzzing, and CI

## 12.1 Test layers

### Unit tests

Test each runtime module directly.

### Golden tests

For fixed inputs, compare reference and fast outputs.

### Property tests

Generate random structured inputs and compare:

```ocaml
let prop_apply input =
  let r1 = Reference.apply input in
  let r2 = Fast.apply_checked env input in
  normalize r1 = normalize r2
```

### Metamorphic tests

When exact expected output is hard:

```text
encode/decode round trip
parse/print/parse stability
cache/no-cache equivalence
commuting independent state updates
handler order invariants where valid
```

### Fault injection

Test runtime failures:

```text
missing key
bad bytes
out-of-bounds index
I/O error
unhandled effect
exception in callback
cache corruption simulation
```

## 12.2 Differential test generation from Rocq

The code generator should emit test generators from type declarations where possible:

```coq
Class Gen (A : Type) := gen : seed -> A * seed.
```

Generated OCaml calls the same generator or a corresponding QCheck generator. The important part is sharing the input distribution and seed reproduction.

## 12.3 CI gates

Minimum gates:

```text
make rocq              # proofs and reference specs
make extract-ref       # slow reference model
make gen-fast          # OCaml direct-style code
make build-fast        # dune build
make test              # unit and differential tests
make fuzz-smoke        # bounded fuzzing on every PR
make tcb-report        # manifest and assumption diff
make bench-smoke       # no catastrophic regression
```

Nightly gates:

```text
long fuzz campaigns
large corpus replay
allocation profiling
runtime stress with handler nesting
mutated runtime tests
cross-platform tests when int width matters
```

## 12.4 Determinism

For blockchain/protocol code, determinism matters. Avoid runtime dependencies that vary across machines unless abstracted:

- hash randomization;
- map iteration order;
- clock;
- locale;
- filesystem ordering;
- floating point edge cases;
- platform-dependent `int` width.

Use deterministic wrappers where needed.

# 13. Performance engineering

## 13.1 What to measure

For every hot entrypoint:

```text
wall-clock time
minor allocations
major allocations
promoted words
maximum live words
handler suspension count
exception count
branch count where possible
bytes copied
array bounds checks if measurable
```

## 13.2 Handler overhead discipline

Effect handlers are efficient, but not free. Avoid:

- one handler per tiny function;
- effect operations in inner loops when a local mutable value is enough;
- using effects for pure function calls;
- repeatedly crossing C callback boundaries with effects.

Prefer specializing handlers away when the handler is known:

```coq
with_local_counter (fun c => incr c ;; incr c ;; get c)
```

can generate:

```ocaml
let c = ref 0 in
incr c; incr c; !c
```

rather than repeated `perform` operations.

## 13.3 Allocation targets

For a hot generated function, inspect:

- closure allocation from higher-order binds;
- tuple allocation from state threading;
- option allocation in inner loops;
- bytes copying;
- list construction where arrays would work;
- GADT witness allocation.

The direct-style generator should eliminate most bind closures and state pairs.

## 13.4 Native data policy

Use proof-friendly representations in Rocq and runtime-friendly representations in OCaml:

```text
Rocq list              -> OCaml array/bytes for hot sequential data
Rocq FMap              -> OCaml Map or Hashtbl depending on determinism
Rocq nat               -> int only for fuel/bounds, never as default data type
Rocq Prop invariants   -> runtime debug assertions or erased proofs
Rocq dependent pairs   -> records/GADTs where runtime witness needed
```

## 13.5 Benchmark acceptance criteria

For each module, define a baseline and budget:

```text
reference model: correctness only, no performance budget
fast model:      <= target latency and allocation budget
regression:      fail PR if > 10 percent on stable benchmark
```

Do not optimize without allocation data. For OCaml, most wins will come from representation choices, removing closure allocation, avoiding intermediate lists, and improving locality.

# 14. Repository layout

Suggested layout:

```text
rocq-effectful-extraction/
  theories/
    Effects/
      Signature.v
      Prog.v
      Sum.v
      Laws.v
      Hoare.v
      ITreeBridge.v
    RuntimeSpec/
      BytesSpec.v
      Int63Spec.v
      ArrayRegionSpec.v
      ErrorSpec.v
      TraceSpec.v
      CacheSpec.v
    Examples/
      KV.v
      Encoding.v
      Parser.v
  codegen/
    dune
    src/
      eff_ir.ml
      read_json.ml
      typecheck_ir.ml
      emit_ocaml.ml
      emit_mli.ml
      emit_manifest.ml
      emit_tests.ml
      main.ml
  runtime/
    dune
    runtime_int63.mli
    runtime_int63.ml
    runtime_bytes.mli
    runtime_bytes.ml
    runtime_array_region.mli
    runtime_array_region.ml
    runtime_error.mli
    runtime_error.ml
    runtime_trace.mli
    runtime_trace.ml
    runtime_cache.mli
    runtime_cache.ml
    runtime_effect_safety.mli
    runtime_effect_safety.ml
    runtime_gadt_witness.mli
    runtime_gadt_witness.ml
  generated/
    README.md
  tests/
    unit/
    differential/
    fuzz/
    corpus/
  bench/
  ci/
    check_tcb.sh
    check_no_unregistered_extract.sh
    check_no_forbidden_unsafe.sh
  docs/
    runtime_manifest.schema.json
    design.md
    tcb.md
```

# 15. Implementation roadmap

## Phase 0: Scaffolding

Deliverables:

- Dune workspace.
- Rocq theory skeleton for `Prog`, effect signatures, and handlers.
- OCaml runtime skeleton.
- CI scripts for TCB checks.
- One example effect: `ErrorE`.

Exit criteria:

- Rocq builds.
- OCaml runtime builds.
- TCB report exists.
- No generated fast code yet.

## Phase 1: Deep DSL and reference interpreter

Deliverables:

- `Prog` deep embedding.
- `KV`, `Error`, `Env`, `Trace` effect signatures.
- Pure reference handlers.
- Basic laws and Hoare layer.
- Extracted reference interpreter.

Exit criteria:

- A nontrivial `KV` example is proved and extracted.
- Reference execution works in OCaml.

## Phase 2: Effect IR and direct-style OCaml generator

Deliverables:

- JSON or S-expression export from the deep embedding.
- `EffIR` typechecker.
- OCaml code emitter.
- `.mli` emitter.
- Manifest emitter.
- KV example generated to direct style.

Exit criteria:

- Generated fast KV example compiles.
- Reference vs fast differential tests pass.
- Generated code contains no free monad constructors.

## Phase 3: Runtime modules for native data

Deliverables:

- `Runtime_bytes`.
- `Runtime_array_region`.
- `Runtime_error`.
- `Runtime_trace`.
- `Runtime_cache`.

Exit criteria:

- Parser or encoder example uses bytes/buffer natively.
- Local mutable array example is pure at the boundary.
- Differential tests cover native modules.

## Phase 4: GADT witnesses

Deliverables:

- `Runtime_gadt_witness`.
- Typed encoding example.
- Equality witness support.
- Ban broad `Obj.magic`.

Exit criteria:

- Typed encoder/decoder compiles with GADTs.
- No generated `Obj.magic`.
- Any handwritten cast is isolated and reviewed.

## Phase 5: Recognized Gallina lowering

Deliverables:

- MetaRocq-based recognizer or plugin.
- Lowering from monadic Gallina to `EffIR`.
- Error messages for unsupported constructs.

Exit criteria:

- Users can write natural monadic definitions.
- Deep DSL remains available as a fallback.

## Phase 6: Production hardening

Deliverables:

- Long fuzz campaigns.
- Benchmark suite.
- Runtime manifest review process.
- Documentation for contributors.
- Integration pilot in one real subsystem.

Exit criteria:

- One meaningful protocol or infrastructure component runs through the pipeline.
- Performance is within an agreed factor of handwritten OCaml.
- TCB report is stable and reviewed.

# 16. Detailed tasks for a code agent

## Task group A: Rocq core

1. Create `theories/Effects/Signature.v` with type-indexed effect signatures.
2. Create `theories/Effects/Prog.v` with `Ret`, `Op`, `bind`, `trigger`, and notations.
3. Prove monad laws up to extensional equality for terminating `Prog`.
4. Create `theories/Effects/Sum.v` for explicit effect sums.
5. Create `theories/Effects/Laws.v` with law classes.
6. Create `theories/Effects/Hoare.v` with `Spec`, `verifies`, sequencing rules, and frame-like rules for independent effects.
7. Create `theories/Examples/KV.v` with `Get`, `Put`, `Delete`, reference handler, and example proofs.
8. Create `theories/Examples/Error.v` with exception-like behavior.
9. Create `theories/RuntimeSpec/BytesSpec.v` with abstract bytes operations and simple laws.
10. Add `Print Assumptions` CI output for every example theorem.

## Task group B: IR export

1. Define a serializable AST for the deep `Prog` fragment.
2. Implement a Rocq-side command or extraction path that writes JSON/S-expressions.
3. Include type names, effect operation names, argument names, and return types.
4. Reject higher-order values unless explicitly whitelisted.
5. Emit stable hashes of source declarations.
6. Add tests that compare emitted IR snapshots.

## Task group C: OCaml code generator

1. Implement `eff_ir.ml`.
2. Implement `typecheck_ir.ml` to verify operation arities and return types.
3. Implement `emit_ocaml.ml` for expressions.
4. Implement `emit_effects.ml` for `type _ Effect.t += ...` declarations.
5. Implement `emit_handlers.ml` for simple handlers.
6. Implement `emit_mli.ml` for public signatures.
7. Implement `emit_manifest.ml`.
8. Implement `emit_tests.ml` for differential test scaffolding.
9. Add pretty-printing with deterministic formatting.
10. Fail codegen on unsupported constructs with actionable errors.

## Task group D: Runtime

1. Implement `Runtime_error` with exception backend and checked runner.
2. Implement `Runtime_effect_safety` with `Effect.Unhandled` conversion.
3. Implement `Runtime_bytes` with safe and unsafe APIs separated.
4. Implement `Runtime_array_region` with region-like abstraction.
5. Implement `Runtime_trace` with deterministic trace collection.
6. Implement `Runtime_cache` with clear observational contract.
7. Implement `Runtime_gadt_witness` with type witnesses and equality.
8. Add module-level tests for each runtime component.
9. Add forbidden API grep checks.
10. Add benchmark hooks.

## Task group E: Differential testing

1. Build extracted reference executable.
2. Build generated fast executable.
3. Define normalized result comparison.
4. Implement random generators for example input types.
5. Implement seed replay.
6. Add corpus tests.
7. Add fuzz smoke tests on every PR.
8. Add nightly long fuzz tests.
9. Add fault injection tests.
10. Store failing inputs as corpus entries.

## Task group F: Safety and TCB automation

1. Implement `ci/check_tcb.sh`.
2. Fail on unregistered `Extract Constant`.
3. Fail on `Obj.magic` outside approved files.
4. Fail on raw `Effect.perform` outside generated/runtime files.
5. Fail on C `external` declarations unless registered.
6. Generate `tcb_report.md`.
7. Diff `tcb_report.md` in CI.
8. Require owner labels for new runtime primitives.
9. Require benchmark entries for hot-path primitives.
10. Require proof or test entries for every manifest primitive.

# 17. Worked example: key-value state effect

## 17.1 Rocq source

```coq
From Effects Require Import Prog Hoare.

Parameter key : Type.
Parameter value : Type.
Parameter value_zero : value.
Parameter value_succ : value -> value.

Variant KV : Type -> Type :=
| Get    : key -> KV (option value)
| Put    : key -> value -> KV unit
| Delete : key -> KV unit.

Definition get (k : key) : Prog KV (option value) :=
  trigger (Get k).

Definition put (k : key) (v : value) : Prog KV unit :=
  trigger (Put k v).

Definition incr (k : key) : Prog KV unit :=
  ox <- get k;;
  match ox with
  | None => put k (value_succ value_zero)
  | Some x => put k (value_succ x)
  end.
```

## 17.2 Reference semantics

```coq
Parameter map : Type.
Parameter find : key -> map -> option value.
Parameter add : key -> value -> map -> map.
Parameter remove : key -> map -> map.

Definition handle_kv {A} (op : KV A) (s : map) : A * map :=
  match op with
  | Get k => (find k s, s)
  | Put k v => (tt, add k v s)
  | Delete k => (tt, remove k s)
  end.

Fixpoint run_kv {A} (p : Prog KV A) (s : map) : A * map :=
  match p with
  | Ret x => (x, s)
  | Op _ op k =>
      let '(x, s') := handle_kv op s in
      run_kv (k x) s'
  end.
```

## 17.3 Generated effects

```ocaml
module KV_effect : sig
  type key = Runtime_key.t
  type value = Runtime_value.t

  type _ Effect.t +=
    | Get : key -> value option Effect.t
    | Put : key * value -> unit Effect.t
    | Delete : key -> unit Effect.t

  val get : key -> value option
  val put : key -> value -> unit
  val delete : key -> unit
end = struct
  type key = Runtime_key.t
  type value = Runtime_value.t

  type _ Effect.t +=
    | Get : key -> value option Effect.t
    | Put : key * value -> unit Effect.t
    | Delete : key -> unit Effect.t

  let get k = Effect.perform (Get k)
  let put k v = Effect.perform (Put (k, v))
  let delete k = Effect.perform (Delete k)
end
```

## 17.4 Generated direct-style function

```ocaml
let incr k =
  match KV_effect.get k with
  | None -> KV_effect.put k (Runtime_value.succ Runtime_value.zero)
  | Some x -> KV_effect.put k (Runtime_value.succ x)
```

## 17.5 Runtime handler

```ocaml
open Effect.Deep

let run table f =
  try f () with
  | effect (KV_effect.Get k), kcont ->
      continue kcont (Hashtbl.find_opt table k)
  | effect (KV_effect.Put (k, v)), kcont ->
      Hashtbl.replace table k v;
      continue kcont ()
  | effect (KV_effect.Delete k), kcont ->
      Hashtbl.remove table k;
      continue kcont ()
```

## 17.6 Differential test

```ocaml
let prop_incr seed =
  let input = Gen_kv_state.from_seed seed in
  let ref_state = Reference_kv.run_incr input in
  let fast_state =
    let table = Runtime_kv.table_of_model input in
    Runtime_kv.run table (fun () -> Generated.incr input.key);
    Runtime_kv.model_of_table table
  in
  Model.equal ref_state fast_state
```

## 17.7 Contract

```text
Runtime_KV.run refines run_kv if:
- Runtime_key equality matches Rocq key equality.
- Runtime_value operations match Rocq value operations.
- Hashtbl observable contents match the finite-map model.
- Handler resumes each continuation exactly once.
- No unhandled KV effects escape run.
```

# 18. Worked example: typed protocol encoding

## 18.1 Rocq view

```coq
Parameter encoding : Type -> Type.
Parameter bytes : Type.
Parameter error : Type.

Parameter encode : forall A, encoding A -> A -> bytes.
Parameter decode : forall A, encoding A -> bytes -> result A error.

Axiom decode_encode : forall A (e : encoding A) (x : A),
  decode A e (encode A e x) = Ok x.
```

## 18.2 OCaml GADT runtime

```ocaml
type _ encoding =
  | Int64 : int64 encoding
  | Bytes : bytes encoding
  | Pair : 'a encoding * 'b encoding -> ('a * 'b) encoding
  | List : 'a encoding -> 'a list encoding

let rec encode : type a. a encoding -> a -> bytes = fun e x ->
  match e with
  | Int64 -> Encode_int64.run x
  | Bytes -> Encode_bytes.run x
  | Pair (a, b) ->
      let x1, x2 = x in
      Encode_pair.run (encode a x1) (encode b x2)
  | List a ->
      Encode_list.run (List.map (encode a) x)

let rec decode : type a. a encoding -> bytes -> (a, error) result = fun e b ->
  match e with
  | Int64 -> Decode_int64.run b
  | Bytes -> Decode_bytes.run b
  | Pair (a, c) -> Decode_pair.run (decode a) (decode c) b
  | List a -> Decode_list.run (decode a) b
```

## 18.3 Reasoning and trust

Two possible trust policies:

1. **Reference-first.** Implement a Rocq reference encoder/decoder and prove `decode_encode`. Generate or test OCaml against the reference. This is preferred.
2. **Native-contract.** Treat the OCaml GADT encoder/decoder as a runtime realizer and accept `decode_encode` as an executable TCB axiom. Use heavy differential tests and corpus replay.

For protocol-critical serialization, prefer reference-first for the data format and native-contract for the byte-level buffer implementation.

# 19. Risks and mitigations

## 19.1 Runtime does not match Rocq semantics

Mitigation:

- same `EffIR` for reference and fast code;
- differential tests;
- manifest hashes;
- strict runtime contracts;
- small runtime modules;
- fuzzing and corpus replay.

## 19.2 Effects leak outside handlers

Mitigation:

- generated checked entrypoints;
- CI grep for raw `Effect.perform`;
- runtime wrapper for `Effect.Unhandled`;
- explicit handler order in manifest.

## 19.3 Misuse of one-shot continuations

Mitigation:

- restrict v1 to first-order handlers that resume exactly once;
- ban multi-shot backtracking through effects;
- linter for handlers;
- code review for scheduler-like handlers.

## 19.4 Performance worse than expected

Mitigation:

- direct-style codegen, not free monad execution;
- benchmark early;
- specialize handlers away for inner loops;
- use bytes/arrays/refs in ST regions;
- inspect allocations.

## 19.5 TCB grows silently

Mitigation:

- generated `tcb_report.md`;
- CI diff;
- owner labels;
- LOC budgets;
- ban unregistered primitives.

## 19.6 GADT witness module becomes an unsafe dumping ground

Mitigation:

- one module only;
- no exported unsafe casts;
- code review by type-system experts;
- property tests for equality witnesses;
- prefer fully typed implementations.

## 19.7 General Gallina lowering becomes too hard

Mitigation:

- deep DSL first;
- keep recognized fragment small;
- treat unsupported constructs as codegen errors;
- use MetaRocq only when the MVP is stable.

# 20. References

[R1] Rocq Prover 9.2 documentation, Program extraction.  
https://rocq-prover.org/doc/V9.2.0/refman/addendum/extraction.html

[R2] Rocq Prover documentation, Primitive objects.  
https://rocq-prover.org/doc/master/refman/language/core/primitive.html

[R3] Coq standard library, `ExtrOcamlNatInt`, efficient but uncertified realizers for `nat`.  
https://rocq-prover.org/doc/v8.9/stdlib/Coq.extraction.ExtrOcamlNatInt.html

[R4] MetaRocq verified extraction repository.  
https://github.com/MetaRocq/rocq-verified-extraction

[R5] Rocq Papers, Verified Extraction from Coq to OCaml.  
https://rocq-prover.org/papers/verified-extraction-from-coq-to-ocaml

[R6] OCaml manual 5.5, Effect handlers.  
https://ocaml.org/manual/5.5/effects.html

[R7] OCaml manual, Generalized algebraic datatypes.  
https://ocaml.org/manual/5.2/gadts-tutorial.html

[R8] OCaml documentation, Memory representation of values.  
https://ocaml.org/docs/memory-representation

[R9] OCaml manual, Bytes module.  
https://ocaml.org/manual/5.3/api/Bytes.html

[R10] Interaction Trees: Representing Recursive and Impure Programs in Coq.  
https://www.research.ed.ac.uk/en/publications/interaction-trees-representing-recursive-and-impure-programs-in-c/

[R11] FreeSpec, Modular verification of programs with effects and effect handlers.  
https://link.springer.com/article/10.1007/s00165-020-00523-2

[R12] Lean reference manual, Elaboration and Compilation.  
https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/

[R13] Zoo: A Framework for the Verification of Concurrent OCaml 5 Programs using Separation Logic.  
https://researchportal.ip-paris.fr/en/publications/zoo-a-framework-for-the-verification-of-concurrent-ocaml-5-progra/

[R14] rocq-of-ocaml.  
https://github.com/formal-land/rocq-of-ocaml

[R15] Octez documentation, Generalized Algebraic Data Types.  
https://octez.tezos.com/docs/developer/gadt.html

# Appendix A. MVP acceptance checklist

The MVP is acceptable when all boxes below are true:

```text
[ ] Rocq deep DSL supports Ret, Bind, Trigger, Match, and simple recursion.
[ ] KV, Error, Env, Trace effects are defined in Rocq.
[ ] Pure reference handlers exist and have basic laws.
[ ] One nontrivial example has a Rocq proof against reference semantics.
[ ] IR export is deterministic.
[ ] OCaml generator emits direct-style code.
[ ] OCaml runtime handlers compile under OCaml 5.3+.
[ ] Reference and fast implementations pass differential tests.
[ ] TCB report is generated and checked in CI.
[ ] Obj.magic is absent or isolated in a single reviewed witness module.
[ ] No unregistered Extract Constant exists.
[ ] Public entrypoints catch unhandled effects.
[ ] Benchmark smoke test confirms no free-monad interpreter in hot path.
```

# Appendix B. Design maxims

1. The proof target is the reference handler, not the OCaml handler.
2. The OCaml handler is trusted, tested, and kept small.
3. Generate direct style, never production free monads.
4. Native data types are allowed only through registered realizers.
5. GADTs are the preferred way to preserve useful type indices at runtime.
6. Effects are for modular control and boundaries, not every local variable.
7. Multi-shot semantics must be explicit, not smuggled through OCaml continuations.
8. Every trust expansion must appear in the TCB report.
9. Every hot-path claim must have a benchmark.
10. Every runtime primitive must have an owner.
