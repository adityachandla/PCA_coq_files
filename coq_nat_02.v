(* Exercise coq_nat_02 *)

(* In the previous exercise we defined natural numbers and a plus
   operation on them. As a matter of fact those definitions (and
   many more) are part of the standard library of Coq, see:
     http://coq.inria.fr/library-eng.html
   They are part of the core library which is loaded automatically
   when Coq is started.
*)
Print nat.
Print plus.

(* Moreover Coq introduces notations for natural numbers allowing
   to write '0' for zero (instead of the letter 'O'), '+' for
   'plus' (with the infix notation) and to use decimal numbers
   instead of the unary notation with 'S'. *)
Check (2 + 2).

(* In the previous exercise we proved that '0 + n = n' and a very
   simple proof it was. Now let us try to prove 'n + 0 = n'. This
   is slightly more difficult. Can you see why? How would you prove
   that? *)

Lemma plus_zero_r : forall n, n + 0 = n.

Proof.
intros.
induction n.
(* You can also do
     elim n
   which is is the "primitive" tactic, but then you have to do additional
   intros
  You can also do 
     destruct n
  but that doesn't give you an induction hypothesis, only case distinction
*)
simpl.
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.

Qed.
