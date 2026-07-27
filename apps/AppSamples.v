(** * AppSamples — the application PROGRAMS: wc, the HTTP/1.0 server, the concurrent driver.

    Specific programs written WITH the generic Rocqeteer library, kept OUT of the
    installed [theories/] library (which stays domain-independent).  The PROOFS about
    them live in [RocqeteerApps.FileIO] / [SockIO] / [SchedHttp]; this file holds the
    [tm] values and the codegen's combined program lists: [all_programs_full] is the
    generic [Samples.all_programs] followed by the applications, and the two proven
    tower elaborations (Expiry [Elab.elab]; the full consolidation+Expiry
    [ElabNs.elab_full], adr-0016) over that SAME combined list drive mode-K codegen. *)
From Stdlib Require Import ZArith List String Ascii.
From Rocqeteer Require Import EffIR Samples Elab ElabNs.
Import ListNotations.
Local Open Scope Z_scope.

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

(** C5 (adr-0019): the CONCURRENT driver's two fibers, as EffIR programs so the
    codegen emits them (theories/SchedHttp.v proves that under a run-to-completion
    schedule they recover [http_prog]'s transcript).  The ACCEPTOR accepts a
    connection and hands the whole accept result (a [Tag] at db0) to the worker over
    channel 0; the WORKER receives it and runs the SAME per-connection handler the
    sequential server uses.  [drv_acceptor]/[drv_worker] are the fuel-3 instances the
    concurrent tool and its differential run (accept fuel = client count, the harness
    contract). *)
Definition acceptor (fc : nat) : tm :=
  Repeat fc (Bind (Perform OAccept []) (Perform OChanSend [VInt 0; VVar 0])).
Definition worker (fw fr : nat) (ml : Z) : tm :=
  Repeat fw (Bind (Perform OChanRecv [VInt 0])
               (Match (VVar 0) [(PTag 0, http_handle fr ml)] (Ret VUnit))).
Definition drv_acceptor : tm := acceptor 3.
Definition drv_worker : tm := worker 3 8 7.

(** The application program registry (the entries lifted out of [Samples.all_programs]). *)
Definition app_programs : list (string * tm) :=
  [ ("sample_wc"%string, sample_wc);
    ("sample_wc_big"%string, sample_wc_big);
    ("sample_file_rw"%string, sample_file_rw);
    ("sample_file_missing"%string, sample_file_missing);
    ("sample_http"%string, sample_http);
    ("sample_http_big"%string, sample_http_big);
    ("drv_acceptor"%string, drv_acceptor);
    ("drv_worker"%string, drv_worker) ].

(** The codegen's source-of-truth: generic demos ++ applications, and the two proven
    tower elaborations over the same list (mode F / mode K, adr-0016). *)
Definition all_programs_full : list (string * tm) :=
  Samples.all_programs ++ app_programs.
Definition elab_programs_full : list (string * tm) :=
  List.map (fun nt => (fst nt, Elab.elab (snd nt))) all_programs_full.
Definition elab_full_programs_full : list (string * tm) :=
  List.map (fun nt => (fst nt, ElabNs.elab_full (snd nt))) all_programs_full.
