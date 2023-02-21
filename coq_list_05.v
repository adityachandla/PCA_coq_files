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
  (***** write the body of the function here *****)   
  
(* Now let us try this definition for an empty list and for
   lists of length 1 and 2. *)

Lemma reverse_nil : reverse nil = nil.

Proof.
  (*! proof *)

Qed.

Lemma reverse_one_elt : forall a, 
  reverse (cons a nil) = cons a nil.
  
Proof.
  (*! proof *)
  
Qed.

Lemma reverse_two_elts : forall a b,
  reverse (cons a (cons b nil)) = cons b (cons a nil).
  
Proof.
  (*! proof *)
  
Qed.