(** * Gallery — sockets: [OAccept] · [ORecv] · [OSend] · [OCloseConn]  (C4, adr-0018)

    Connections are SCRIPTED: the world carries the ordered per-connection input
    streams (determinism by injection — the adr-0011 pattern, and the C5
    recorded-schedule mechanism in miniature); [OAccept] pops the script, chunked
    [ORecv] reuses the file discipline (EMPTY chunk = the client's half-close),
    and the transcript of finished connections is THE observable.

    The flagship theorem is [SockIO.http_prog_correct]: the HTTP/1.0 server
    program computes, for EVERY route table, EVERY connection script, and every
    covering fuel/chunk size, exactly the reference response per connection.
    The instances below pin its corners; tests/diff_sock.ml replays the same
    scripts over REAL loopback TCP against the generated server, and tools/rhttpd
    serves real clients with the same proven core. *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR Samples SockIO.
Import ListNotations.
Local Open Scope Z_scope.

(** A hit, a miss, and a malformed request — the whole transcript equals the
    spec (ids in accept order, inputs preserved, responses exact). *)
Theorem serve_three :
  observe_sock (encode_table tb) [req_ok; req_404; req_bad] sample_http
  = (ORet DUnit, expected_log tb [req_ok; req_404; req_bad]).
Proof. vm_compute. reflexivity. Qed.

(** The request line straddling a recv-chunk boundary changes nothing — the
    accumulate-then-parse discipline (and, generally, [chunking_invariance]). *)
Theorem serve_straddled :
  observe_sock (encode_table tb) [req_straddle] sample_http
  = (ORet DUnit, expected_log tb [req_straddle]).
Proof. vm_compute. reflexivity. Qed.

(** Script exhaustion is the EAGAIN VALUE, not an error: a bounded accept loop
    over a short script just no-ops the remaining fuel. *)
Theorem serve_exhausted :
  observe_sock (encode_table tb) [req_ok] sample_http
  = (ORet DUnit, expected_log tb [req_ok]).
Proof. vm_compute. reflexivity. Qed.
