(* Exercise coq_nat_09 *)

(* Now, let us prove that multiplication is commutative *)

(* For this we may need to use some properties of addition and multiplication  
   that we proved before. *)
Require Import Arith.
Check mult_0_r.
Check plus_comm.
Check plus_assoc.

(* ... and a following auxiliary lemma *)

Lemma mult_succ : forall m n, n + n * m = n * S m.
Proof.
 (*! proof *)
Qed.

Lemma mult_comm : forall m n, m * n = n * m.

Proof.
 (*! proof *)

Qed.
