Section predicate_logic.
Variable D: Set.
Variable c d e :D.
Variable P Q T: D-> Prop.


Theorem example_12 : (exists x, ~ P x) -> ~forall x, P x.
Proof.
intros.
intro H1.
destruct H as [y H]. (* For this y the proposition holds *)
 (* this replaces the assumption 
       "exists x : D, ~ P x" 
    by a fresh variable y :D and a hypothesis H : ~ P y
    also try 
       "elim H" and then "intros" and compare.
   Note that [y H] describes the "intro pattern" for exists: 
   we get two pieces of data, y : D and H : ~ P y
  *)
apply H.
apply H1.
  (* apply applies a "unification algorithm": 
     The "P x" in "H : forall x : D, P x" is unified with the goal "P y", 
     which means that and instantiation for the universally quatified x
     is found such that P x equals P y.
     That is: we take y for x in the hypothesis H 
   *)
Qed.

Theorem pred_023 : ((exists x, P x) -> forall x, Q x) -> 
  forall y, P y  -> Q y.
Proof.
intros.
apply H.
exists y.
  (* This says that we take "y" for the existentially quantified variable 
     in the goal
         "exists x : D, P x"
   *)
assumption.
Qed.

Theorem pred_008 : ~(forall x, P x)  -> ~ forall x, P x /\ Q x.
Proof.
intros.
intro H1.
apply H.
apply H1.
Qed.

Theorem coq_pred_015 : 
  ~(forall x : D, P x \/ (Q x -> T x)) -> ~forall x : D, T x.
Proof.
intros.
intro H1.
apply H.
right.
intros.
apply H1.
Qed.


Theorem pred_025 : ~(forall x, P x /\ Q x) /\ (forall x, P x) -> 
  ~forall x, Q x.
Proof.
intros.
intro H1.
apply H.
split.
destruct H as [H2 H3].
apply H3.
apply H1.
Qed.

(* Note how a binary relation on D is declared in Coq *)
Variable R : D -> D -> Prop.

Theorem pred_031 : (forall x, P x /\ Q x) -> forall x, P x \/ exists y, R x y.
Proof.
intros.
left.
(* destruct H. *)
destruct (H x).
assumption.
Qed.


Theorem pred_036 : (exists x, forall y, ~R x y) -> ~forall x, R x x.
Proof.
intros.
intro H1.
destruct H.
destruct (H x).
apply H1.
Qed.


Theorem pred_013 : (exists x, P x \/ Q x) -> (forall x, ~Q x) -> exists x, P x.
Proof.
intros.
destruct H.
destruct H.
exists x.
assumption.
absurd (Q x).
apply (H0 x).
assumption.
Qed.

Theorem pred_035 : (forall y, Q y -> ~exists x, P x) /\ (forall x, P x) -> forall y, ~Q y.
Proof.
intros.
intro.
destruct H.
destruct (H y).
assumption.
exists y.
apply H1.
Qed.

(* more difficult *)
Theorem pred_016 : (forall x, P x \/ R x x) -> (forall x, P x -> exists y, R x y /\ R y x) -> forall x, exists y, R x y.
Proof.
intros.
destruct (H x).
destruct (H0 x).
assumption.
exists x0.
destruct H2.
assumption.
exists x.
assumption.
Qed.

Theorem pred_067 : (forall x, ~P x) -> ~exists x, P x.
Proof.
intros.
intro.
destruct H0.
apply (H x).
assumption.
Qed.

(* Predicate logic with equality *)

Theorem example_14 : forall x y, R y y /\ x = y -> R y x.
Proof.
intros.
destruct H as [H1 H2].
rewrite <- H2 in H1. (* Use an equality in other equation *)
rewrite <- H2.
 (* This replaces x by y in the goal
    Also try
      "rewrite <- H2"
    and see what happens
    Also try
      "rewrite <- H2 in H1"
    and see what happens
  *)
assumption.
Qed.


Variable W : D -> D -> D -> Prop.

Theorem example_17 : forall x y, W x x y /\ x = y -> W x y y.
Proof.
intros.
destruct H.
rewrite <- H0 in H.
rewrite <- H0.
assumption.
Qed.


Theorem pred_059 : (forall x:D, forall y, x = y) -> (exists x, P x) -> forall x, P x.
Proof.
intro H0.
intro H1.
intro x.
destruct H1.
rewrite <- (H0 x x0) in H.
assumption.
Qed.

Theorem pred_058 : (forall x:D, forall y, x = y) /\ P d -> P e.
Proof.
intros.
destruct H.
rewrite <- (H e d) in H0.
assumption.
Qed.

Section pred_080.

Hypothesis Domain : forall x, (x = c \/ x = d \/ x = e).

Theorem pred_080 : (forall x, P x) -> P e /\ P d /\ P c.
Proof.
intros.
split.
apply (H e).
split.
apply (H d).
apply (H c).
Qed.


End pred_080.

(*CHALLENGE PROBLEM
    This theorem shows that if we have a transitive
   relation on a 3-element set, and if each element has
   a successor, then some element must be reflexive for
   this relation *)

Section pred_078.

Hypothesis Domain : exists x1, exists x2, exists x3, forall x:D, (x = x1 \/ x = x2 \/ x = x3).
Hypothesis Successor : forall x, exists y, R x y.
Hypothesis Transitive : forall x, forall y, forall z, R x y /\ R y z -> R x z.

Theorem pred_078 : exists x, R x x.
Proof.
Admitted.

End pred_078.


End predicate_logic.
