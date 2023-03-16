(* Exercise coq_list_02 *)

(* Those are the definitions from the previous exercise: *)

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint append (l m : natlist) {struct l} : natlist :=
  match l with
  | nil => m
  | cons x xs => cons x (append xs m)
  end.
  
(* Now let us prove that the append operation is associative *)

Lemma append_assoc : forall l m n,
  append (append l m) n = append l (append m n).

Proof.
intros.
induction l.
* simpl.
  reflexivity.
* simpl. (*Simplifying the cons*)
  rewrite IHl.
  reflexivity.
Qed.

