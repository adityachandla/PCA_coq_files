(* Exercise coq_list_06 *)

(* Those are the definitions from the previous exercise: *)

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint append (l m : natlist) {struct l} : natlist :=
  match l with
  | nil => m
  | cons x xs => cons x (append xs m)
  end.

Fixpoint length (l : natlist) : nat :=
 (* copy your definition from the previous exercise here *)

Fixpoint reverse (l : natlist) : natlist :=
 (* copy your definition from the previous exercise here *)

(* Now let us prove that reverse does not change the length
   of a list *)

(* For this we may need a result proven in one of the previous
   exercises and some results about natural numbers (remember
   the exercises concerning natural numbers?) *)
Axiom append_length : forall l m,
  length (append l m) = length l + length m.
Require Import Arith.

Lemma reverse_length : forall l,
  length l = length (reverse l).
  
Proof.
  (*! proof *)
  
Qed.