(* Exercise coq_nat_01 *)

(* Let us give a definition of natural numbers.
   '0' is a natural number and if 'n' is a natural number, then
   the successor of 'n' is also a natural numbers.
   This is expressed in Coq by the following inductive definition:
   (note that we use the letter 'O' for zero) *)
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
  
(* This definition introduces a new type 'nat': *)
Check nat.

(* It also introduces two constructors for this type.
   'O' that is just a natural number *)
Check O.

(* and 'S' that is a function that given natural number returns
   another natural number - the successor *)
Check S.

(* Now to do something interesting we need some operations on
   nat. Let us start with addition. To define 'm + n' we proceed
   by doing case analysis on 'm'. We have two cases corresponding
   to the two constructors of type 'nat'. If 'm' is '0' then the 
   result is simply 'n'. Otherwise 'm' is a successor of some 
   number 'p' and 'S p + n' equals 'S (p + n)'. This is expressed
   in Coq with the following recursive definition: *)
Fixpoint plus (m n : nat) {struct m} : nat :=
  match m with
  | O => n
  | S p => S (plus p n)
  end.

Print plus.

(* For such recursive definition to be accepted by Coq it must be
   terminating, ie. it is not allowed that the sequence of
   recursive calls can go on forever. To ensure this Coq uses a
   very simple criterion - one of the arguments must be structuraly
   decreasing along the recursive call. The annotation '{struct m}'
   in the above definition is used to indicated that 'm' is the
   decreasing argument. Indeed in the second case the first argument
   to 'plus' equals 'S p' and is replaced by 'p' in the recursive
   call *)
   
(* Let us check the type of 'plus' *)   
Check plus.

(* We can also see its full definition *)
Print plus.

(* Now let us prove a simple lemma stating that 'O' is a neutral
   element for addition. *)

Lemma plus_zero_l : forall n, plus O n = n.

Proof.
intros.
unfold plus.
reflexivity.
 
Qed.
