(* Exercise coq_list_01 *)

(* In exercises coq_nat_* we were dealing with natural 
   numbers. Not let us define lists of natural numbers.
   Such a list is either empty, 'nil', or it is a natural
   number 'a' followed by a list 'l' - 'cons a l'. *)
Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(* Remark: lists are defined in the standard library of
   Coq but that definition is polymorphic, ie. for every
   type 'A', 'list A' gives a type of lists with elements
   of type 'A'. *)

(* Now let us define some operations on such lists. 
   Let's start with an append function that given two lists
   concatenates them. *)
Fixpoint append (l m : natlist) {struct l} : natlist :=
  match l with
  | nil => m
  | cons x xs => cons x (append xs m)
  end.
  
(* Now let us prove how append works with empty lists *)

Lemma append_nil_l : forall l, append nil l = l.

Proof.
Admitted.

Lemma append_nil_r : forall l, append l nil = l.
Proof.
Admitted.
