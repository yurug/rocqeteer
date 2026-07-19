(** * Gallery — files: [OOpen] · [ORead] · [OFWrite] · [OClose]  (C3, adr-0017)

    Byte-stream I/O over descriptors on a PURE in-world file system: paths are
    resolved only at [OOpen] (inode pinning is structural), reads return
    deterministic chunks — the EMPTY chunk is EOF, no sentinel — and the modeled
    failures (ENOENT on read-open, EBADF on stale descriptors) are tagged VALUES
    a program branches on, never aborts.  Everything environmental lives in the
    realizer behind named, partly runtime-checked assumptions
    (docs/runtime_manifest.toml: Runtime_FS_*, Runtime_File*_full).

    The flagship theorem is [FileIO.wc_prog_correct]: the wc-core computes the
    exact byte count for EVERY path, contents, fuel and chunk size covering the
    file — chunk size is provably unobservable ([FileIO.chunking_invariance]).
    The instances below are its EOF-boundary corners, runnable by [vm_compute].

    Deep dive: theories/FileIO.v; the tool is tools/rwc.ml (compared against
    coreutils `wc -c` by tests/diff_file.ml, through real files). *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR Samples FileIO.
Import ListNotations.
Local Open Scope Z_scope.

(** Write two chunks, reopen, read back: the file region behaves like a file. *)
Theorem write_then_read_roundtrip :
  fst (run [] sample_file_rw (init_world DUnit 0))
  = ORet (DPair (DBytes (list_ascii_of_string "hello!")) (DBool true)).
Proof. vm_compute. reflexivity. Qed.

(** EOF boundaries for chunk size 3 at sizes 5 / 6 / 7: the count is exact on
    either side of a chunk multiple (the < mutant dies here — theories/FileIO.v
    [wc_mutant_rejected]). *)
Theorem wc_at_boundaries :
     fst (run [] (wc_prog 8 3) (fio_world (bytes_n 5))) = ORet (DInt 5)
  /\ fst (run [] (wc_prog 8 3) (fio_world (bytes_n 6))) = ORet (DInt 6)
  /\ fst (run [] (wc_prog 8 3) (fio_world (bytes_n 7))) = ORet (DInt 7).
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The modeled failures are VALUES: a missing path opens to Tag(1,2) (the
    ENOENT convention) and a stale descriptor probes to Tag(1,9) (EBADF) —
    the program returns both, aborting nothing. *)
Theorem modeled_errors_are_values :
  fst (run [] sample_file_missing (init_world DUnit 0))
  = ORet (DPair (DTag 1 (DInt 2)) (DTag 1 (DInt 9))).
Proof. vm_compute. reflexivity. Qed.
