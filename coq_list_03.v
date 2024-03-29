(* Exercise coq_list_03 *)

(* Those are the definitions from the previous exercise: *)

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint append (l m : natlist) {struct l} : natlist :=
  match l with
  | nil => m
  | cons x xs => cons x (append xs m)
  end.
  
(* Now let us define the length function that returns the 
   length of a given list. *)

Fixpoint length (l : natlist) {struct l} : nat :=
  (***** write the body of a function here *****)
  match l with
  | nil => 0
  | cons x xs => 1 + length xs
  end.
(* Now let us try this definition on two simple examples.
   (Hint: usually this is a good idea to do that with newly 
   introduced definitions) *)

Lemma length_nil : length nil = 0.

Proof.
  unfold length.
  reflexivity.
Qed.

Lemma length_3 : forall a b c,
  length (cons a (cons b (cons c nil))) = 3.
  
Proof.
  intros.
  simpl.
reflexivity.
  
Qed.