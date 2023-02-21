(* Exercise coq_nat_08 *)

(* Now, let us prove that '1' is neutral for multiplication *)

(* Remember the properties of addition we were using? They may
   come in handy in this exercise. To get access to many results
   concerning arithmetic of natural number (including properties
   of addition and multiplication) we load the library 'Arith' *)
Require Import Arith.
	    
Lemma mult_1_l : forall n, 1 * n = n.

Proof.

 (*! proof *)

Qed.

Lemma mult_1_r : forall n, n * 1 = n.

Proof.
 (*! proof *)

Qed.