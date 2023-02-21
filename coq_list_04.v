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
  
Fixpoint length (l : natlist) : nat :=
  (* copy your definition from the previous exercise here *)
  
(* Now let us prove that the length of two concatenated 
   lists is the sum of the lengths of those lists. *)

Lemma length_append : forall l m,
  length (append l m) = length l + length m.
  
Proof.
  (*! proof *)
Qed.