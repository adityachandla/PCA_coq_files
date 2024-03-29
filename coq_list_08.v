(* Exercise coq_list_08 *)

(* Those are the definitions from the previous exercise: *)

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint append (l m : natlist) {struct l} : natlist :=
  match l with
  | nil => m
  | cons x xs => cons x (append xs m)
  end.

Fixpoint reverse (l : natlist) : natlist :=
  match l with
  | nil => nil
  | cons ele rem => append (reverse rem) (cons ele nil)
  end.

(* Now, let us prove that reversing a list twice gives back
   the original list. *)
   
(* For that we may need the result proven in the previous
   exercise *)   
Axiom reverse_append : forall l m,
  reverse (append l m) = append (reverse m) (reverse l).
      
Lemma reverse_double : forall l, reverse (reverse l) = l.
    
Proof.
  intros.
  induction l.
  simpl; reflexivity.
  simpl.
  rewrite reverse_append.
  rewrite IHl.
  simpl.
  reflexivity.
Qed.