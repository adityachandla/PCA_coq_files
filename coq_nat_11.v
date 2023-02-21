(* Exercise coq_nat_11 *)

(* Do you know that having stamps of nominals 3 and 5 you can
   pay any value greater or equal than 8? 
   Below is a Coq specification of this statemant - can you
   prove it? *)
Require Import Arith.

(* Hint: for arithmetical reasoning you may try to use the 
         'lia' tactic. If you do that you will only get
	 Correct for this exercise (and not Solved), as this 
	 is one of the powerful automated Coq tactics, that 
	 are in principle not allowed to be used for solving
	 those exercises. In this case, however, it is ok
	 to use lia.
	 
   Remark: if afterwards you decide to try to prove it without
           the use of lia, it should give you a good idea
	   of how helpful such automated tactics can be!
*)   
Require Import Lia.

Lemma stamps : forall i, exists v3, exists v5, i + 8 = 3*v3 + 5*v5.

Proof.
(* ! *)
Qed.

