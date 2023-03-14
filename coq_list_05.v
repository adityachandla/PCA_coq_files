(* Exercise coq_list_05 *)

(* Those are the definitions from the previous exercise: *)

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint append (l m : natlist) {struct l} : natlist :=
  match l with
  | nil => m
  | cons x xs => cons x (append xs m)
  end.

(* Now define a function 'reverse' that given a list returns
   the list with the elements in the reversed order. *)
Fixpoint reverse (l : natlist) : natlist :=
  match l with 
  | nil => nil
  | cons s rem => append (reverse rem) (cons s nil)
  end.

Lemma reverse_nil : reverse nil = nil.

Proof.
  unfold reverse.
  reflexivity.

Qed.

Lemma reverse_one_elt : forall a, 
  reverse (cons a nil) = cons a nil.
  
Proof.
  intros.
  unfold reverse.
  simpl.
reflexivity.
Qed.

Lemma reverse_two_elts : forall a b,
  reverse (cons a (cons b nil)) = cons b (cons a nil).
  
Proof.
  intros.
  simpl.
  reflexivity.
Qed.