(** * Gallery — durability: [OJournal]

    [OJournal v] appends [(now, v)] to a write-only log: no op reads it, so
    journaling can NEVER change a program's result — that independence is the
    proven-general frame law (theories/Journal.v, [run_journal_frame]), and it
    is what makes append-only-file persistence a safe afterthought: a consumer
    journals each effective command and REPLAYS the log at the recorded
    instants to reconstruct the store (the redoq server's recovery is exactly
    this, proven end-to-end).

    Deep dive: theories/Journal.v (frame law + run-sequence fold lemma). *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

Definition k : list ascii := list_ascii_of_string "k".

(** Journal an intent alongside the write; entries carry the run instant.
    (The journal is newest-first internally.) *)
Definition journaled_set : tm :=
  Bind (Perform OPut [VBytes k; VInt 3])
       (Perform OJournal [VPair (VBytes (list_ascii_of_string "set")) (VInt 3)]).

Theorem entries_carry_the_instant :
  let '(_, w) := run_top DUnit 777 journaled_set in
  w.(journal) = [(777, DPair (DBytes (list_ascii_of_string "set")) (DInt 3))].
Proof. vm_compute. reflexivity. Qed.

(** Journaling is invisible to results and the store — one instance of the
    general frame law proven in theories/Journal.v for EVERY program. *)
Theorem journaling_changes_nothing_observable :
  observe DUnit 0 journaled_set
  = observe DUnit 0 (Perform OPut [VBytes k; VInt 3]).
Proof. vm_compute. reflexivity. Qed.

(** Entries survive a later abort: what was journaled before the throw is
    still there (no rollback — the durability point). *)
Theorem pre_throw_entries_survive :
  let '(o, w) := run_top DUnit 5
    (Bind (Perform OJournal [VInt 1]) (Perform OThrow [VInt 9])) in
  o = OErr (DInt 9) /\ w.(journal) = [(5, DInt 1)].
Proof. vm_compute. split; reflexivity. Qed.
