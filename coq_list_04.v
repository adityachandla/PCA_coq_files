(* Exercise coq_list_04 *)

(* Those are the definitions from the previous exercise: *)

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint append (l m : natlist) {struct l} : natlist :=
  match l with
  | nil => m
  | cons x xs => cons x (append xs m)
  end.
  
Fixpoint length (l : natlist) {struct l} : nat :=
  match l with
  | nil => 0
  | cons s l => 1 + length l
  end.

Lemma length_append : forall l m,
  length (append l m) = length l + length m.
  
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.