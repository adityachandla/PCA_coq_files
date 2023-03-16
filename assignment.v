Require Import Arith.

Inductive tree : Set :=
| leaf : tree
| node : tree -> nat -> tree -> tree.

Fixpoint all_leq(n: nat)(t: tree): Prop :=
  match t with
    | leaf => True
    | node l val r => (val <= n) /\ (all_leq n l) /\ (all_leq n r)
  end.

Fixpoint all_geq(n: nat)(t: tree): Prop := 
  match t with
    | leaf => True
    | node l val r => (val > n) /\ (all_geq n l) /\ (all_geq n r)
  end. 

Fixpoint bst (T: tree): Prop :=
  match T with
  | leaf => True
  | node l v r => (all_leq v l) /\ (all_geq v r) /\ bst l /\ bst r
end.

Fixpoint insert(n: nat)(T: tree): tree :=
  match T with
  | leaf => node leaf n leaf
  | node l v r => if Nat.leb n v then (insert n l) else (insert n r)
  end.

(*Print Nat.*)

Lemma insert_correctness: forall t: tree, forall n: nat, bst t -> bst (insert n t).
Proof.
intros.
induction t.
* simpl.
  auto.
* simpl insert.
  destruct (n <=? n0).
  apply IHt1.
  destruct H as [H1 [H2 [H3 H4]]].
  auto.
  apply IHt2.
  destruct H as [H1 [H2 [H3 H4]]].
  auto.
Qed.


Fixpoint to_list(T: tree): (list nat) :=
  match T with
    | leaf => nil
    | node l v r => (to_list l) ++  (cons v nil) ++ (to_list r)
  end.

Fixpoint list_min(l: (list nat)): (option nat) := 
  match l with
    | nil => None
    | cons x rem => match (list_min rem) with
      | None => (Some x)
      | Some y => if x <? y then (Some x) else (Some y)
      end
  end.
Fixpoint sort_list(l: (list nat)): (list nat) := 


Fixpoint tree_from_list(l: (list nat)): tree := 
   match l with
    | nil => leaf
    | cons x rem => node leaf x (tree_from_list rem)
  end.

(*Keep finding min and recurse on the right side*)  


