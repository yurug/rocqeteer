(** Sample EffIR programs that exercise codegen/runtime paths [prog0] does not:
    [ODelete], a top-level [Ret], multiple [Perform]s to distinct keys, a negative key
    literal, and depth-2 de Bruijn nesting. Consumed by the multi-program differential
    test (audit finding 1) so those lowering rules are covered, not dead. Store keys are
    byte strings since R4 (decimal bytes of the former integer keys, adr-0011 §Decision 5).

    R7 (adr-0010-structured-values) adds [sample_tag_build] (constructs DTag/DList) and
    [sample_tag_dispatch] (matches on DTag via PTag).

    R4+R5 (adr-0011-time-and-expiring-store) add [sample_store]/[sample_ttl]/
    [sample_put_clears]/[sample_persist]/[sample_setdl_missing] (the expiring store ops)
    and [sample_now] (the Time effect + deadline arithmetic via PAddChecked).

    R6 (adr-0012-list-elimination) adds the [Fold] samples ([sample_fold_put]/
    [sample_fold_ovf]/[sample_fold_concat]/[sample_fold_trace]/[sample_fold_guard]) and
    the R8-confirmation throw-payload samples ([sample_throw_bytes]/[sample_throw_tagged]).
    Proven in theories/Fold.v.

    R9 (adr-0013-journal-effect) adds [sample_journal] (mixed-shape journal entries,
    one appended inside a Fold body) and [sample_journal_throw] (Repeat-driven appends,
    then a throw — pre-throw entries survive). Proven in theories/Journal.v.

    R12 (adr-0009 discipline, ADR-free prim addition) adds [sample_ci_dispatch]
    (case-INSENSITIVE token dispatch: Env token -> PLowerBytes -> Match on lowercase
    literals + default — the consumer driver: SET-style option tokens are
    case-insensitive on the oracle, inexpressible with the exact PEqBytes).
    Proven in theories/Prims.v §6.

    R13 (adr-0009 discipline, ADR-free prim addition) adds [sample_fold_collect]
    (the COLLECTING FOLD: an argv-style DList of byte keys folded with acc = the reply
    DList under construction, body = OGet + PListSnoc a tagged slot — replies of
    DATA-DEPENDENT length with zero new term forms). Proven in theories/Fold.v §9. *)

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

(* ===== R6 samples (adr-0012-list-elimination) + R8 confirmation ============= *)

(** FOLD body shared by the R6 samples: put the CURRENT ELEMENT at the key
    [print(acc)] (the accumulator is a DInt counter, so elements land at keys
    "0", "1", "2", … in iteration order), then step the counter via PAddChecked.

    de Bruijn discipline inside a Fold body (adr-0012 §Decision 1): on entry
    db0 = acc, db1 = elem (push_env [elem; acc]). Annotated per step:
      Bind (Prim PPrintInt [acc=db0])        — then db0 = print result, db1 = acc, db2 = elem
      Match PSome (binds the key bytes)      — then db0 = key, db1 = print result,
                                                    db2 = acc, db3 = elem
      Bind (Perform OPut [key=db0; elem=db3]) — then db0 = put unit, …, db3 = acc, db4 = elem
      Bind (Prim PAddChecked [acc=db3; 1])   — then db0 = add result
      Match PSome -> Ret db0 (the next acc); DNone (overflow) -> OThrow ovf_bytes.
    The PPrintInt default arm (DNone — impossible for an in-range counter) throws
    err_bytes so a violation would be loudly observable. *)
Definition fold_put_body : tm :=
  Bind (Prim PPrintInt [VVar 0])
  (Match (VVar 0)
     [(PSome,
        (* db0 = key bytes, db1 = print result, db2 = acc, db3 = elem *)
        Bind (Perform OPut [VVar 0; VVar 3])
        (* db0 = put unit, db1 = key, db2 = print result, db3 = acc, db4 = elem *)
        (Bind (Prim PAddChecked [VVar 3; VInt 1])
           (Match (VVar 0)
              [(PSome, Ret (VVar 0))]           (* db0 = acc+1 = the next acc *)
              (Perform OThrow [VBytes ovf_bytes]))))]
     (Perform OThrow [VBytes err_bytes])).

(** FOLD (R6, adr-0012): fold the CONTEXT list with the effectful body above —
    each element is Put at its iteration-index key; the result is the element
    count (DInt n). Non-DList context: empty fold, result DInt 0, no puts. *)
Definition sample_fold_put : tm :=
  Bind (Perform OAsk [])
       (Fold (VVar 0) (Ret (VInt 0)) fold_put_body).

(** FOLD accumulator-overflow path: same body, but the counter STARTS at int64_max,
    so the first element overflows PAddChecked and the body throws ovf_bytes (the
    element itself is still Put first — exactly the pre-abort effects commit).
    Empty/non-list context: result DInt int64_max, no puts. *)
Definition sample_fold_ovf : tm :=
  Bind (Perform OAsk [])
       (Fold (VVar 0) (Ret (VInt int64_max)) fold_put_body).

(** FOLD order observability via a NON-COMMUTATIVE accumulator (PBytesConcat):
    acc ++ elem, left to right — a list of byte strings and its reverse yield
    observably different bytes. db0 = acc, db1 = elem. *)
Definition sample_fold_concat : tm :=
  Bind (Perform OAsk [])
       (Fold (VVar 0) (Ret (VBytes [])) (Prim PBytesConcat [VVar 0; VVar 1])).

(** FOLD order observability via the TRACE: emit each element left to right; the
    accumulator is untouched (init DUnit, body returns it). After the OTrace Bind,
    db0 = unit, db1 = acc, db2 = elem — the body result Ret (VVar 1) is the acc. *)
Definition sample_fold_trace : tm :=
  Bind (Perform OAsk [])
       (Fold (VVar 0) (Ret VUnit)
             (Bind (Perform OTrace [VVar 1]) (Ret (VVar 1)))).

(** FOLD error short-circuit: like [sample_fold_put], but a poison element
    ("BAD") makes the body THROW — the fold aborts mid-list with OErr, and the
    store shows EXACTLY the puts of the elements before the poison. The PBytes
    guard binds 0 variables, so the default arm sees db0 = acc, db1 = elem
    unchanged and can be [fold_put_body] verbatim. *)
Definition poison_bytes : list ascii := list_ascii_of_string "BAD".

Definition sample_fold_guard : tm :=
  Bind (Perform OAsk [])
       (Fold (VVar 0) (Ret (VInt 0))
             (Match (VVar 1)
                [(PBytes poison_bytes, Perform OThrow [VBytes poison_bytes])]
                fold_put_body)).

(** R8 CONFIRMATION (theories/Fold.v §R8): error values carry arbitrary dvals —
    including exact byte-string messages — and have since R1/M1 ([OThrow] takes any
    val; [OErr e] carries any dval). These two samples make that DELIBERATE:
    [sample_throw_bytes] aborts with an exact DBytes message after one committed
    put; [sample_throw_tagged] aborts with a DTag-structured payload (tag 2 over
    a (message, code) pair). *)
Definition throw_msg_bytes : list ascii := list_ascii_of_string "boom: k missing".

Definition sample_throw_bytes : tm :=
  Bind (Perform OPut [VBytes key1; VInt 1])
       (Perform OThrow [VBytes throw_msg_bytes]).

Definition sample_throw_tagged : tm :=
  Perform OThrow [VTag 2 (VPair (VBytes throw_msg_bytes) (VInt 404))].

(* ===== R9 samples (adr-0013-journal-effect) ================================= *)

(** JOURNAL (R9, adr-0013): [sample_journal] appends MIXED-SHAPE entries — a DBytes
    message, a DTag-structured "command" (tag 5 over a (bytes, code) pair), then one
    entry per CONTEXT list element via a Fold body (further shapes, incl. nested
    DTag/DList, come from the context). The Fold body is sample_fold_trace-shaped:
    on entry db0 = acc, db1 = elem; after the OJournal Bind, db0 = unit, db1 = acc,
    db2 = elem — the body result Ret (VVar 1) is the acc (DUnit throughout). All
    entries share the run's single instant (adr-0011: no in-IR clock advancement).
    Entry order + timestamps + the frame law are proven in theories/Journal.v. *)
Definition jmsg_bytes : list ascii := list_ascii_of_string "j-open".
Definition jtag_bytes : list ascii := list_ascii_of_string "SETX".

Definition sample_journal : tm :=
  Bind (Perform OJournal [VBytes jmsg_bytes])
  (Bind (Perform OJournal [VTag 5 (VPair (VBytes jtag_bytes) (VInt 3))])
  (Bind (Perform OAsk [])
        (Fold (VVar 0) (Ret VUnit)
              (Bind (Perform OJournal [VVar 1]) (Ret (VVar 1)))))).

(** JOURNAL error short-circuit (R9): a Repeat body increments key "0" and journals the
    freshly-read counter (DSome 1 then DSome 2 — Repeat entry ORDER is genuinely
    observable, not two equal entries), then the program THROWS; the post-throw append
    never runs, so exactly the k = 2 pre-throw entries survive (OErr commits prior
    state, adr-0013 §implementers). *)
Definition jboom_bytes : list ascii := list_ascii_of_string "j-boom".

Definition sample_journal_throw : tm :=
  Bind (Repeat 2 (Bind (incr_at key0)
                       (Bind (Perform OGet [VBytes key0])
                             (Perform OJournal [VVar 0]))))
       (Bind (Perform OThrow [VBytes jboom_bytes])
             (Perform OJournal [VInt 99])).

(* ===== R12 sample (adr-0009 discipline — PLowerBytes/PUpperBytes) =========== *)

(** CASE-INSENSITIVE DISPATCH (R12): read an option token from the context (Env),
    case-fold it via PLowerBytes, then dispatch on the LOWERCASE byte literals —
    "nx" -> DInt 1, "xx" -> DInt 2, anything else -> DInt 0 (the mandatory default).
    So "NX"/"nX"/"Nx"/"nx" all take the first branch: one branch per token instead of
    one per capitalization (the 2^n blowup exact PEqBytes/PBytes would force).
    de Bruijn: db0 = folded token in the Match; db1 = the raw token.
    A non-DBytes context makes PLowerBytes yield DNone -> default -> DInt 0.
    Each branch is proven in theories/Prims.v §6. *)
Definition nx_bytes : list ascii := list_ascii_of_string "nx".
Definition xx_bytes : list ascii := list_ascii_of_string "xx".

Definition sample_ci_dispatch : tm :=
  Bind (Perform OAsk [])
  (Bind (Prim PLowerBytes [VVar 0])
        (Match (VVar 0)
           [(PBytes nx_bytes, Ret (VInt 1));
            (PBytes xx_bytes, Ret (VInt 2))]
           (Ret (VInt 0)))).

(* ===== R13 sample (adr-0009 discipline — PListSnoc) ========================== *)

(** COLLECTING FOLD (R13): build a reply of DATA-DEPENDENT length. The context is an
    argv-style DList of byte KEYS; the accumulator is the reply DList under
    construction (init [VList []]); the body OGets the current key and snocs ONE
    tagged slot onto the acc:
      hit  (DSome v) -> DTag 1 v      ("bulk": the stored value, any shape)
      miss (DNone)   -> DTag 0 DUnit  ("nil": the key is absent/expired)
    One slot per key, ORDER PRESERVED — the MGET-shaped consumer driver: Fold (R6)
    eliminates lists, PListSnoc is what CONSTRUCTS one whose length is only known at
    runtime; zero new term forms. A non-DList context makes the fold empty (result =
    the init [DList []], adr-0012 §Decision 2 posture).

    de Bruijn (body entry: db0 = acc, db1 = key — push_env [elem; acc]):
      Bind (Perform OGet [key=db1])   — then db0 = lookup, db1 = acc, db2 = key
      Match PSome (binds the value)   — then db0 = v, db1 = lookup, db2 = acc
      PNone / default                 — db0 = lookup, db1 = acc (0 binders)
    The Prim result IS the branch body's result = the next accumulator.
    Proven end-to-end for a concrete seeded store in theories/Fold.v §9 (order, nil
    slots, length = argv length, prepend mutant rejected). *)
Definition sample_fold_collect : tm :=
  Bind (Perform OAsk [])
       (Fold (VVar 0) (Ret (VList []))
             (Bind (Perform OGet [VVar 1])
                   (Match (VVar 0)
                      [(PSome, Prim PListSnoc [VVar 2; VTag 1 (VVar 0)]);
                       (PNone, Prim PListSnoc [VVar 1; VTag 0 VUnit])]
                      (Prim PListSnoc [VVar 1; VTag 0 VUnit])))).

(** SINGLE SOURCE OF TRUTH for the program list. The codegen iterates this (so it emits one
    [let name () = …] per entry), and extraction of it pulls every referenced sample as a
    named value. Adding a program is THEN a one-line edit here — no separate codegen or
    extraction list to keep in sync (kb/spec/codegen.md; tooling iteration). *)

(* ===== C3 (adr-0017): the file family samples + the wc-core program ========== *)

(** The counter key of the wc loop. *)
Definition wc_key : list ascii := list_ascii_of_string "n".

(** One wc-loop iteration; [fd_idx] is the de Bruijn index of the open descriptor
    in the ENCLOSING environment (the Repeat body sees the outer binders).
    Reads a chunk of at most [ml] bytes, adds its length to the store counter.
    The throw arms are unreachable on the good path (proven in FileIO.v); the
    PAddChecked guard makes overflow an abort, never garbage. *)
Definition wc_body (fd_idx : nat) (ml : Z) : tm :=
  Bind (Perform ORead [VVar fd_idx; VInt ml])            (* ch *)
    (Bind (Prim PBytesLen [VVar 0])                      (* ln·ch *)
       (Bind (Perform OGet [VBytes wc_key])              (* cur·ln·ch *)
          (Match (VVar 0)
             [(PSome,                                    (* c·cur·ln·ch *)
               Bind (Prim PAddChecked [VVar 0; VVar 2])  (* s·c·cur·ln·ch *)
                 (Match (VVar 0)
                    [(PSome, Perform OPut [VBytes wc_key; VVar 0])]
                    (Perform OThrow [VBytes (list_ascii_of_string "OVF")])))]
             (Perform OThrow [VBytes (list_ascii_of_string "NOCTR")])))).

(** wc-core (byte count): open the ctx path read-only, zero the counter, read up
    to [fuel] chunks of [ml] bytes accumulating lengths, close, return the count.
    A failed open THROWS the open result (the Tag(1, ENOENT) value) — the shell
    wrapper's exit-code material.  Correct for files of size <= fuel*ml
    (FileIO.v [wc_prog_correct]). *)
Definition wc_prog (fuel : nat) (ml : Z) : tm :=
  Bind (Perform OAsk [])                                 (* p *)
    (Bind (Perform OOpen [VVar 0; VInt 0])               (* r·p *)
       (Match (VVar 0)
          [(PTag 0,                                      (* fd·r·p *)
            Bind (Perform OPut [VBytes wc_key; VInt 0])  (* u·fd·r·p *)
              (Bind (Repeat fuel (wc_body 1 ml))
                 (Bind (Perform OClose [VVar 2])         (* cl·rep·u·fd·r·p *)
                    (Bind (Perform OGet [VBytes wc_key])
                       (Match (VVar 0)
                          [(PSome, Ret (VVar 0))]
                          (Perform OThrow
                             [VBytes (list_ascii_of_string "NOCTR")]))))))]
          (Perform OThrow [VVar 0]))).

(** Small-instance twin for the differential suites (tiny fuel/chunk so the
    adversarial corpora exercise many EOF boundaries). *)
Definition sample_wc : tm := wc_prog 8 3.

(** The TOOL instance (tools/rwc.ml): 64 chunks of 512 bytes — correct for files
    up to 32 KiB by [FileIO.wc_prog_correct]; the cap is stated, not hidden. *)
Definition sample_wc_big : tm := wc_prog 64 512.

(** Write-then-read lifecycle: create "out", write two chunks, close, reopen for
    read, read back a chunk, close — returns (readback, close-flags). *)
Definition sample_file_rw : tm :=
  Bind (Perform OOpen [VBytes (list_ascii_of_string "out"); VInt 1])
    (Match (VVar 0)
       [(PTag 0,                                          (* fd·r *)
         Bind (Perform OFWrite [VVar 0; VBytes (list_ascii_of_string "hel")])
           (Bind (Perform OFWrite [VVar 1; VBytes (list_ascii_of_string "lo!")])
              (Bind (Perform OClose [VVar 2])
                 (Bind (Perform OOpen [VBytes (list_ascii_of_string "out"); VInt 0])
                    (Match (VVar 0)
                       [(PTag 0,                          (* fd2·r2·cl·w2·w1·fd·r *)
                         Bind (Perform ORead [VVar 0; VInt 100])
                           (Bind (Perform OClose [VVar 1])
                              (Ret (VPair (VVar 1) (VVar 0)))))]
                       (Perform OThrow [VVar 0]))))))]
       (Perform OThrow [VVar 0])).

(** The modeled-error VALUES: open a missing path (Tag(1,2)) and probe a stale
    fd (Tag(1,9)) — programs branch on these, no abort. *)
Definition sample_file_missing : tm :=
  Bind (Perform OOpen [VBytes (list_ascii_of_string "absent"); VInt 0])
    (Bind (Perform ORead [VInt 77; VInt 10])
       (Ret (VPair (VVar 1) (VVar 0)))).


(* ===== C4 (adr-0018): the sockets samples + the HTTP/1.0 server ============= *)

(** Wire constants: Rocq string literals cannot carry CR/LF, so the delimiters are
    built from [ascii_of_nat]. *)
Definition crlf : list ascii := [ascii_of_nat 13; ascii_of_nat 10].
Definition crlfcrlf : list ascii := crlf ++ crlf.
Definition sp1 : list ascii := [" "%char].
Definition get_sp : list ascii := list_ascii_of_string "GET ".
Definition hbkey : list ascii := list_ascii_of_string "b".
Definition nobuf : list ascii := list_ascii_of_string "NOBUF".

Definition resp_400 : list ascii :=
  list_ascii_of_string "HTTP/1.0 400 Bad Request" ++ crlf
  ++ list_ascii_of_string "Content-Length: 0" ++ crlfcrlf.
Definition resp_404 : list ascii :=
  list_ascii_of_string "HTTP/1.0 404 Not Found" ++ crlf
  ++ list_ascii_of_string "Content-Length: 0" ++ crlfcrlf.
Definition resp200_pre : list ascii :=
  list_ascii_of_string "HTTP/1.0 200 OK" ++ crlf
  ++ list_ascii_of_string "Content-Length: ".

(** Route lookup as a collecting [Fold] over the injected table (ctx = a [DList]
    of [DPair path body]) — first hit wins; the matched body is returned, or 404/
    400 built here.  ENTRY convention: the PATH is at de Bruijn 0.  The whole
    subtree references NOTHING below its entry point, so it splices anywhere. *)
Definition http_route : tm :=
  Bind (Perform OAsk [])                                (* tbl·path *)
    (Bind (Fold (VVar 0) (Ret VNone)
             (* body env: acc(0)·elem(1)·tbl(2)·path(3) *)
             (Match (VVar 0)
                [(PSome, Ret (VSome (VVar 0)))]         (* already found: keep *)
                (Match (VVar 1)
                   [(PPair,                             (* b(0)·q(1)·acc·elem·tbl·path *)
                     Bind (Prim PEqBytes [VVar 1; VVar 5])
                       (Match (VVar 0)
                          [(PBool true, Ret (VSome (VVar 1)))]
                          (Ret VNone)))]
                   (Ret VNone))))
       (* f·tbl·path *)
       (Match (VVar 0)
          [(PSome,                                      (* body·f·tbl·path *)
            Bind (Prim PBytesLen [VVar 0])              (* bl·body *)
              (Bind (Prim PPrintInt [VVar 0])           (* pd·bl·body *)
                 (Match (VVar 0)
                    [(PSome,                            (* ds·pd·bl·body *)
                      Bind (Prim PBytesConcat [VBytes resp200_pre; VVar 0])
                        (Bind (Prim PBytesConcat [VVar 0; VBytes crlfcrlf])
                           (Bind (Prim PBytesConcat [VVar 0; VVar 5])
                              (Ret (VVar 0)))))]
                    (Ret (VBytes resp_400)))))]        (* print fail: unreachable *)
          (Ret (VBytes resp_404)))).

(** Parse the accumulated request and COMPUTE the response bytes — a pure value
    computation with the BUFFER at de Bruijn 0 at entry and no other external
    references (the connection id never appears here; adr-0018 §6).  Failure
    arms all yield 400. *)
Definition http_parse : tm :=
  Bind (Prim PFindSub [VVar 0; VBytes crlf])            (* f·buf *)
    (Match (VVar 0)
       [(PSome,                                         (* i·f·buf *)
         Bind (Prim PBytesSub [VVar 2; VInt 0; VVar 0]) (* s·i·f·buf *)
           (Match (VVar 0)
              [(PSome,                                  (* line·s·i·f·buf *)
                Bind (Prim PBytesSub [VVar 0; VInt 0; VInt 4])  (* t·line·… *)
                  (Match (VVar 0)
                     [(PSome,                           (* g4·t·line·s·i·f·buf *)
                       Bind (Prim PEqBytes [VVar 0; VBytes get_sp])
                         (* e·g4·t·line — line at 3 *)
                         (Match (VVar 0)
                            [(PBool true,
                              Bind (Prim PBytesLen [VVar 3])       (* ln·e·g4·t·line *)
                                (Bind (Prim PSubChecked [VVar 0; VInt 4])
                                   (* m·ln·e·g4·t·line — line at 5 *)
                                   (Match (VVar 0)
                                      [(PSome,          (* n4·m·ln·e·g4·t·line at 6 *)
                                        Bind (Prim PBytesSub
                                                [VVar 6; VInt 4; VVar 0])
                                          (* r·n4·… *)
                                          (Match (VVar 0)
                                             [(PSome,   (* rest·r·n4·… *)
                                               Bind (Prim PFindSub
                                                       [VVar 0; VBytes sp1])
                                                 (* fj·rest *)
                                                 (Match (VVar 0)
                                                    [(PSome,  (* j·fj·rest at 2 *)
                                                      Bind (Prim PBytesSub
                                                              [VVar 2; VInt 0;
                                                               VVar 0])
                                                        (* q·j·fj·rest *)
                                                        (Match (VVar 0)
                                                           [(PSome, http_route)]
                                                           (Ret (VBytes resp_400))))]
                                                    (Ret (VBytes resp_400))))]
                                             (Ret (VBytes resp_400))))]
                                      (Ret (VBytes resp_400)))))]
                            (Ret (VBytes resp_400))))]
                     (Ret (VBytes resp_400))))]
              (Ret (VBytes resp_400))))]
       (Ret (VBytes resp_400))).

(** Handle ONE connection — the id at de Bruijn 0 at entry: reset the buffer,
    read-to-EOF in [fuel_read] chunks of [ml] (the wc accumulation pattern with
    bytes instead of counts), parse, send ONE response, close.  [conn] appears
    exactly at the two final sites. *)
Definition http_handle (fuel_read : nat) (ml : Z) : tm :=
  Bind (Perform OPut [VBytes hbkey; VBytes []])         (* u·conn *)
    (Bind (Repeat fuel_read
             (Bind (Perform ORecv [VVar 1; VInt ml])    (* ch·u·conn *)
                (Bind (Perform OGet [VBytes hbkey])     (* cur·ch·u·conn *)
                   (Match (VVar 0)
                      [(PSome,                          (* p·cur·ch·u·conn *)
                        Bind (Prim PBytesConcat [VVar 0; VVar 2])
                          (Perform OPut [VBytes hbkey; VVar 0]))]
                      (Perform OThrow [VBytes nobuf])))))
       (* rep·u·conn *)
       (Bind (Perform OGet [VBytes hbkey])              (* g·rep·u·conn *)
          (Match (VVar 0)
             [(PSome,                                   (* buf·g·rep·u·conn at 4 *)
               Bind http_parse                          (* resp·buf·…·conn at 5 *)
                 (Bind (Perform OSend [VVar 5; VVar 0])
                    (Perform OCloseConn [VVar 6])))]
             (Perform OThrow [VBytes nobuf])))).

(** The sequential server: a bounded accept loop; script exhaustion (the EAGAIN
    value) makes an iteration a no-op — total by construction (adr-0018 §2). *)
Definition http_prog (fuel_conns fuel_read : nat) (ml : Z) : tm :=
  Repeat fuel_conns
    (Bind (Perform OAccept [])
       (Match (VVar 0)
          [(PTag 0, http_handle fuel_read ml)]
          (Ret VUnit))).

(** Differential-suite instance (tiny chunks: many EOF boundaries) and the tool
    instance (16 connections, 32 KiB requests). *)
Definition sample_http : tm := http_prog 3 8 7.
Definition sample_http_big : tm := http_prog 16 64 512.

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
    ("sample_fold_put"%string, sample_fold_put);
    ("sample_fold_ovf"%string, sample_fold_ovf);
    ("sample_fold_concat"%string, sample_fold_concat);
    ("sample_fold_trace"%string, sample_fold_trace);
    ("sample_fold_guard"%string, sample_fold_guard);
    ("sample_throw_bytes"%string, sample_throw_bytes);
    ("sample_throw_tagged"%string, sample_throw_tagged);
    ("sample_journal"%string, sample_journal);
    ("sample_journal_throw"%string, sample_journal_throw);
    ("sample_ci_dispatch"%string, sample_ci_dispatch);
    ("sample_fold_collect"%string, sample_fold_collect);
    ("sample_wc"%string, sample_wc);
    ("sample_wc_big"%string, sample_wc_big);
    ("sample_file_rw"%string, sample_file_rw);
    ("sample_file_missing"%string, sample_file_missing);
    ("sample_http"%string, sample_http);
    ("sample_http_big"%string, sample_http_big);
    ("demo_prog"%string, demo_prog) ].
