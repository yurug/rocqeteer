(** Sample EffIR programs that exercise codegen/runtime paths [prog0] does not:
    [ODelete], a top-level [Ret], multiple [Perform]s to distinct keys, a negative key
    literal, and depth-2 de Bruijn nesting. Consumed by the multi-program differential
    test (audit finding 1) so those lowering rules are covered, not dead. Store keys are
    byte strings since R4 (decimal bytes of the former integer keys, adr-0011 §Decision 5).

    R7 (adr-0010-structured-values) adds [sample_tag_build] (constructs DTag/DList) and
    [sample_tag_dispatch] (matches on DTag via PTag).

    R4+R5 (adr-0011-time-and-expiring-store) add [sample_store]/[sample_ttl]/
    [sample_put_clears]/[sample_persist]/[sample_setdl_missing] (the expiring store ops)
    and [sample_now] (the Time effect + deadline arithmetic via PAddChecked). *)

From Stdlib Require Import ZArith List String Ascii.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

(** Decimal-bytes key constants (former integer keys; [key7] lives in EffIR.v). *)
Definition key0 : list ascii := list_ascii_of_string "0".
Definition key1 : list ascii := list_ascii_of_string "1".
Definition key2 : list ascii := list_ascii_of_string "2".
Definition key3 : list ascii := list_ascii_of_string "3".
Definition key4 : list ascii := list_ascii_of_string "4".
Definition key5 : list ascii := list_ascii_of_string "5".
Definition key6 : list ascii := list_ascii_of_string "6".
Definition key8 : list ascii := list_ascii_of_string "8".
Definition key9 : list ascii := list_ascii_of_string "9".
Definition keyneg3 : list ascii := list_ascii_of_string "-3".

(** get "2"; if absent put 1, else DELETE "2" — exercises [ODelete] (returns DBool of
    live-removal since R4). *)
Definition sample_delete : tm :=
  Bind (Perform OGet [VBytes key2])
       (Match (VVar 0)
          [(PNone, Perform OPut [VBytes key2; VSucc VZero]);
           (PSome, Perform ODelete [VBytes key2])]
          (Perform OPut [VBytes key2; VSucc VZero])).

(** put "3" := 1 ; put "4" := 2 — two sequential Performs to distinct keys. *)
Definition sample_two : tm :=
  Bind (Perform OPut [VBytes key3; VSucc VZero])
       (Perform OPut [VBytes key4; VSucc (VSucc VZero)]).

(** get "6" ; return it — a top-level [Ret] of a bound variable; state unchanged. *)
Definition sample_ret : tm :=
  Bind (Perform OGet [VBytes key6]) (Ret (VVar 0)).

(** increment at the decimal bytes of a NEGATIVE key — exercises '-'-carrying key bytes. *)
Definition sample_neg : tm := incr_at keyneg3.

(** depth-2 nesting: get "8"; get "9"; match the FIRST result (de Bruijn index 1, under the
    second binder) — exercises de Bruijn shifting the single-Bind prog0 never reaches. *)
Definition sample_nested : tm :=
  Bind (Perform OGet [VBytes key8])
       (Bind (Perform OGet [VBytes key9])
             (Match (VVar 1)
                [(PNone, Perform OPut [VBytes key8; VSucc VZero]);
                 (PSome, Perform OPut [VBytes key8; VSucc (VVar 0)])]
                (Perform OPut [VBytes key8; VSucc VZero]))).

(** ERROR effect: put "1" := 1; THROW 99; put "2" := 2 — the throw aborts, so the second
    put never runs and the state keeps only the pre-throw write. *)
Definition sample_throw : tm :=
  Bind (Perform OPut [VBytes key1; VSucc VZero])
       (Bind (Perform OThrow [VInt 99])
             (Perform OPut [VBytes key2; VSucc (VSucc VZero)])).

(** ERROR + KV composed: get "5"; if absent THROW 7, else increment — one path returns
    normally, the other aborts, so a random state exercises both. *)
Definition sample_guard5 : tm :=
  Bind (Perform OGet [VBytes key5])
       (Match (VVar 0)
          [(PNone, Perform OThrow [VInt 7]);
           (PSome, Perform OPut [VBytes key5; VSucc (VVar 0)])]
          (Perform OThrow [VInt 7])).

(** ENV + KV composed: read the read-only context, then store it at key "1" — exercises
    [OAsk] and that the asked value flows into a Put. *)
Definition sample_env : tm :=
  Bind (Perform OAsk [])
       (Perform OPut [VBytes key1; VVar 0]).

(** TRACE + KV composed: emit 10; put "1" := 1; emit 20 — the trace must record [10; 20]
    in order, and the put must commit, exercising [OTrace] interleaved with KV. *)
Definition sample_trace : tm :=
  Bind (Perform OTrace [VInt 10])
       (Bind (Perform OPut [VBytes key1; VSucc VZero])
             (Perform OTrace [VInt 20])).

(** CACHE + KV composed (memoize): look up key "0" in the cache; on a HIT store the cached
    value at key "1", on a MISS compute [succ zero]=1, cache it at "0", and store it at
    key "1". The KV result (key "1") is the same whether the cache hits or misses with the
    correct value — that observational invisibility is what [theories/Cache.v] proves. *)
Definition sample_cache : tm :=
  Bind (Perform OCacheGet [VBytes key0])
       (Match (VVar 0)
          [(PNone, Bind (Perform OCachePut [VBytes key0; VSucc VZero])
                        (Perform OPut [VBytes key1; VSucc VZero]));
           (PSome, Perform OPut [VBytes key1; VVar 0])]
          (Bind (Perform OCachePut [VBytes key0; VSucc VZero])
                (Perform OPut [VBytes key1; VSucc VZero]))).

(** RECURSION: increment key "0" five times via a bounded loop — exercises [Repeat]. After
    [n] iterations from empty, key "0" holds [n] (proven by induction in theories/Recur.v). *)
Definition sample_count : tm := Repeat 5 (incr_at key0).

(** BYTES: Put a binary-hostile payload (contains NUL, LF, CR) at key "5", then Get it
    back. The literal is built with explicit Ascii constructors so the control characters
    are unambiguous.  NUL = 0x00, LF = 0x0A (b1+b3), CR = 0x0D (b0+b2+b3).
    The byte sequence is: 'h','i', NUL, LF, CR, '!'. *)
Definition bytes_payload : list ascii :=
  [ Ascii false false false true  false true  true  false (* 0x68 = 'h' *)
  ; Ascii true  false false true  false true  true  false (* 0x69 = 'i' *)
  ; Ascii false false false false false false false false (* 0x00 = NUL *)
  ; Ascii false true  false true  false false false false (* 0x0A = LF  *)
  ; Ascii true  false true  true  false false false false (* 0x0D = CR  *)
  ; Ascii true  false false false false true  false false (* 0x21 = '!' *)
  ].

(** put key "5" := bytes_payload; get key "5"; return via Match.
    Result: DBytes bytes_payload; store: {"5" -> (DBytes bytes_payload, None)}. *)
Definition sample_bytes : tm :=
  Bind (Perform OPut [VBytes key5; VBytes bytes_payload])
       (Bind (Perform OGet [VBytes key5])
             (Match (VVar 0)
                [(PNone, Ret VNone);
                 (PSome, Ret (VVar 0))]
                (Ret VNone))).

(** DISPATCH (R2 anti-vacuity): read the context via Env, then dispatch on byte-string
    command names. "GET" -> Ret (VInt 1), "SET" -> Ret (VInt 2), any other -> Ret (VInt 0).
    This exercises [Match] with [PBytes] literal patterns and a first-match-wins default.
    Proven correct by vm_compute in theories/Dispatch.v.

    ASCII encoding (Rocq Ascii b0..b7, LSB-first):
      'G' = 0x47 = 0b01000111: Ascii true true true false false false true false
      'E' = 0x45 = 0b01000101: Ascii true false true false false false true false
      'T' = 0x54 = 0b01010100: Ascii false false true false true false true false
      'S' = 0x53 = 0b01010011: Ascii true true false false true false true false *)
Definition get_bytes : list ascii :=
  [ Ascii.Ascii true  true  true  false false false true false  (* 'G' 0x47 *)
  ; Ascii.Ascii true  false true  false false false true false  (* 'E' 0x45 *)
  ; Ascii.Ascii false false true  false true  false true false  (* 'T' 0x54 *)
  ].

Definition set_bytes : list ascii :=
  [ Ascii.Ascii true  true  false false true  false true false  (* 'S' 0x53 *)
  ; Ascii.Ascii true  false true  false false false true false  (* 'E' 0x45 *)
  ; Ascii.Ascii false false true  false true  false true false  (* 'T' 0x54 *)
  ].

Definition sample_dispatch : tm :=
  Bind (Perform OAsk [])
       (Match (VVar 0)
          [(PBytes get_bytes, Ret (VInt 1));
           (PBytes set_bytes, Ret (VInt 2))]
          (Ret (VInt 0))).

(** DEMO: an "audited counter" composing Env + Trace + recursion + KV. Read an audit tag
    from the read-only context (Env), log it (Trace), bump a hit-counter at key "0" three
    times (Repeat over KV), then persist the tag at key "9" (KV). From context tag 99:
    key "0" = 3, key "9" = 99, trace = [99]. Proven in theories/Demo.v, run end-to-end by
    the demo (make demo). de Bruijn: after Ask the tag is db0; the final Put sees it at db2. *)
Definition demo_prog : tm :=
  Bind (Perform OAsk [])
       (Bind (Perform OTrace [VVar 0])
             (Bind (Repeat 3 (incr_at key0))
                   (Perform OPut [VBytes key9; VVar 2]))).

(** PRIM SAMPLE (R3, adr-0009-vprim-registry): an "INCR-shaped" pipeline using PParseInt64 +
    PAddChecked + PPrintInt.

    Reads a DBytes context (OAsk), tries to parse it as a strict int64 (PParseInt64).
    - On parse success (DSome z): tries to add 1 (PAddChecked).
      - On add success (DSome z'): prints the result (PPrintInt); returns DBytes decimal.
      - On add overflow (DNone): returns DBytes "OVF".
    - On parse failure (DNone): returns DBytes "ERR".

    ERR bytes: 'E','R','R' = 0x45, 0x52, 0x52.
    OVF bytes: 'O','V','F' = 0x4F, 0x56, 0x46. *)
Definition err_bytes : list ascii :=
  [ Ascii.Ascii true  false true  false false false true  false  (* 'E' 0x45 *)
  ; Ascii.Ascii false true  false false true  false true  false  (* 'R' 0x52 *)
  ; Ascii.Ascii false true  false false true  false true  false  (* 'R' 0x52 *)
  ].

Definition ovf_bytes : list ascii :=
  [ Ascii.Ascii true  true  true  true  false false true  false  (* 'O' 0x4F *)
  ; Ascii.Ascii false true  true  false true  false true  false  (* 'V' 0x56 *)
  ; Ascii.Ascii false true  true  false false false true  false  (* 'F' 0x46 *)
  ].

(** [sample_parse]: INCR-pipeline program using PParseInt64 + PAddChecked + PPrintInt.

    Program structure (de Bruijn comments show live bindings at each point):
      Bind (Perform OAsk [])              (* db0 = ctx bytes *)
      (Bind (Prim PParseInt64 [VVar 0])   (* db0 = parse_result, db1 = ctx *)
      (Match (VVar 0)
         [(PNone, Ret (VBytes err_bytes)) (* parse failed *)
          (PSome,                          (* db0 = parsed int, db1 = parse_result, db2 = ctx *)
            Bind (Prim PAddChecked [VVar 0; VInt 1])  (* db0 = add_result, ... *)
            (Match (VVar 0)
               [(PNone, Ret (VBytes ovf_bytes))       (* overflow *)
                (PSome,                                (* db0 = sum, ... *)
                  Bind (Prim PPrintInt [VVar 0])       (* db0 = print_result *)
                  (Match (VVar 0)
                     [(PSome, Ret (VVar 0))]           (* db0 = printed bytes *)
                     (Ret (VBytes err_bytes))))]        (* PPrintInt returned DNone (impossible for in-range) *)
               (Ret (VBytes ovf_bytes))))]
         (Ret (VBytes err_bytes)))). *)
Definition sample_parse : tm :=
  Bind (Perform OAsk [])
  (Bind (Prim PParseInt64 [VVar 0])
  (Match (VVar 0)
     [(PNone, Ret (VBytes err_bytes));
      (PSome,
        Bind (Prim PAddChecked [VVar 0; VInt 1])
        (Match (VVar 0)
           [(PNone, Ret (VBytes ovf_bytes));
            (PSome,
              Bind (Prim PPrintInt [VVar 0])
              (Match (VVar 0)
                 [(PSome, Ret (VVar 0))]
                 (Ret (VBytes err_bytes))))]
           (Ret (VBytes ovf_bytes))))]
     (Ret (VBytes err_bytes)))).

(** STRUCTURED VALUES (R7, adr-0010-structured-values): [sample_tag_build] computes a
    checked-add payload (Prim PAddChecked) and wraps the result in a tagged sum (DTag);
    the success tag additionally pairs the payload with a two-element, MIXED-SHAPE
    [VList] (VInt, VBytes) so [DList] crosses codegen in the same commit as [DTag].

    tag 0 = success, payload = DPair (DInt sum) (DList [DInt 42; DBytes tag_list_bytes])
    tag 1 = overflow, payload = DBytes tag_err_bytes *)
Definition tag_list_bytes : list ascii := list_ascii_of_string "LX".
Definition tag_err_bytes  : list ascii := list_ascii_of_string "TBE".

Definition sample_tag_build : tm :=
  Bind (Perform OAsk [])
  (Bind (Prim PAddChecked [VVar 0; VInt 1])
  (Match (VVar 0)
     [(PNone, Ret (VTag 1 (VBytes tag_err_bytes)));
      (PSome, Ret (VPair (VTag 0 (VVar 0))
                         (VList [VInt 42; VBytes tag_list_bytes])))]
     (Ret (VTag 1 (VBytes tag_err_bytes))))).

(** TAG DISPATCH (R7, anti-vacuity companion to [sample_tag_build]): dispatches on the
    [DTag] constructor via depth-1 [PTag] patterns + the mandatory default arm (same
    first-match-wins / default discipline as adr-0008, applied to the new pattern form
    from adr-0010 §Decision 2). Three observably different outcomes:
      PTag 0 -> tag_dispatch_a_bytes ("TG0")
      PTag 1 -> tag_dispatch_b_bytes ("TG1")
      default -> tag_dispatch_default_bytes ("TDF") — fires on a wrong tag (e.g. DTag 7 _)
                 or on a context that is not a DTag at all (e.g. a bare DInt). *)
Definition tag_dispatch_a_bytes       : list ascii := list_ascii_of_string "TG0".
Definition tag_dispatch_b_bytes       : list ascii := list_ascii_of_string "TG1".
Definition tag_dispatch_default_bytes : list ascii := list_ascii_of_string "TDF".

Definition sample_tag_dispatch : tm :=
  Bind (Perform OAsk [])
       (Match (VVar 0)
          [(PTag 0, Ret (VBytes tag_dispatch_a_bytes));
           (PTag 1, Ret (VBytes tag_dispatch_b_bytes))]
          (Ret (VBytes tag_dispatch_default_bytes))).

(* ===== R4+R5 samples (adr-0011-time-and-expiring-store) ===================== *)

Definition store_key : list ascii := list_ascii_of_string "sk".
Definition ttl_key   : list ascii := list_ascii_of_string "tk".
Definition missing_key : list ascii := list_ascii_of_string "nope".

(** STORE lifecycle: put "sk" := 41; get; delete (DBool of live-removal); get again.
    de Bruijn at the final Ret: db0 = get2, db1 = del, db2 = get1, db3 = put.
    Result (any now): DPair (DSome 41) (DPair (DBool true) DNone). *)
Definition sample_store : tm :=
  Bind (Perform OPut [VBytes store_key; VInt 41])
  (Bind (Perform OGet [VBytes store_key])
  (Bind (Perform ODelete [VBytes store_key])
  (Bind (Perform OGet [VBytes store_key])
        (Ret (VPair (VVar 2) (VPair (VVar 1) (VVar 0))))))).

(** TTL boundary program (the load-bearing one for the now<=d rule): put "tk" := 7;
    set deadline 1000; then (get, get_deadline, delete).
    de Bruijn at the final Ret: db0 = del, db1 = getdl, db2 = get.
    now <= 1000: DPair (DSome 7) (DPair (DSome (DSome 1000)) (DBool true));
    now >  1000: DPair DNone     (DPair DNone                (DBool false)). *)
Definition sample_ttl : tm :=
  Bind (Perform OPut [VBytes ttl_key; VInt 7])
  (Bind (Perform OSetDeadline [VBytes ttl_key; VSome (VInt 1000)])
  (Bind (Perform OGet [VBytes ttl_key])
  (Bind (Perform OGetDeadline [VBytes ttl_key])
  (Bind (Perform ODelete [VBytes ttl_key])
        (Ret (VPair (VVar 2) (VPair (VVar 1) (VVar 0)))))))).

(** OPut CLEARS the deadline (adr-0011 op table): put; set deadline 500; put again;
    get_deadline -> DSome DNone (live, no deadline) at EVERY now — even past 500,
    because the second put replaces the expired binding wholesale. *)
Definition sample_put_clears : tm :=
  Bind (Perform OPut [VBytes ttl_key; VInt 1])
  (Bind (Perform OSetDeadline [VBytes ttl_key; VSome (VInt 500)])
  (Bind (Perform OPut [VBytes ttl_key; VInt 2])
  (Bind (Perform OGetDeadline [VBytes ttl_key])
        (Ret (VVar 0))))).

(** PERSIST (OSetDeadline with VNone): put; set deadline 800; clear it; get_deadline.
    de Bruijn at the final Ret: db0 = getdl, db1 = setdl-None.
    now <= 800: DPair (DBool true)  (DSome DNone)   — cleared while still live;
    now >  800: DPair (DBool false) DNone           — expired before the clear. *)
Definition sample_persist : tm :=
  Bind (Perform OPut [VBytes ttl_key; VInt 3])
  (Bind (Perform OSetDeadline [VBytes ttl_key; VSome (VInt 800)])
  (Bind (Perform OSetDeadline [VBytes ttl_key; VNone])
  (Bind (Perform OGetDeadline [VBytes ttl_key])
        (Ret (VPair (VVar 1) (VVar 0)))))).

(** OSetDeadline on a missing key returns DBool false (no live binding modified). *)
Definition sample_setdl_missing : tm :=
  Bind (Perform OSetDeadline [VBytes missing_key; VSome (VInt 99)])
       (Ret (VVar 0)).

(** TIME (R5): read now (ONow), compute a deadline now+1000 via PAddChecked, return
    DPair now (now+1000) — or DNone on overflow (now near int64_max).
    de Bruijn in the PSome branch: db0 = sum, db1 = add_result, db2 = now. *)
Definition sample_now : tm :=
  Bind (Perform ONow [])
  (Bind (Prim PAddChecked [VVar 0; VInt 1000])
  (Match (VVar 0)
     [(PSome, Ret (VPair (VVar 2) (VVar 0)))]
     (Ret VNone))).

(** SINGLE SOURCE OF TRUTH for the program list. The codegen iterates this (so it emits one
    [let name () = …] per entry), and extraction of it pulls every referenced sample as a
    named value. Adding a program is THEN a one-line edit here — no separate codegen or
    extraction list to keep in sync (kb/spec/codegen.md; tooling iteration). *)
Definition all_programs : list (string * tm) :=
  [ ("prog0"%string, prog0);
    ("sample_delete"%string, sample_delete);
    ("sample_two"%string, sample_two);
    ("sample_ret"%string, sample_ret);
    ("sample_neg"%string, sample_neg);
    ("sample_nested"%string, sample_nested);
    ("sample_throw"%string, sample_throw);
    ("sample_guard5"%string, sample_guard5);
    ("sample_env"%string, sample_env);
    ("sample_trace"%string, sample_trace);
    ("sample_cache"%string, sample_cache);
    ("sample_count"%string, sample_count);
    ("sample_bytes"%string, sample_bytes);
    ("sample_dispatch"%string, sample_dispatch);
    ("sample_parse"%string, sample_parse);
    ("sample_tag_build"%string, sample_tag_build);
    ("sample_tag_dispatch"%string, sample_tag_dispatch);
    ("sample_store"%string, sample_store);
    ("sample_ttl"%string, sample_ttl);
    ("sample_put_clears"%string, sample_put_clears);
    ("sample_persist"%string, sample_persist);
    ("sample_setdl_missing"%string, sample_setdl_missing);
    ("sample_now"%string, sample_now);
    ("demo_prog"%string, demo_prog) ].
