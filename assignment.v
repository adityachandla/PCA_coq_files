Require Import Arith.
Require Import List.
Import ListNotations.


Section TypeAndFunctionDefinitions.
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
    | node l v r => if n <=? v then node (insert n l) v r else node l v (insert n r)
    end.

  Fixpoint occurs(n: nat)(t: tree): Prop :=
    match t with
      | leaf => False
      | node l v r => v = n \/ occurs n l \/ occurs n r
    end.

  Definition occurs_opt(n: option nat)(t: tree): Prop :=
    match n with
      | None => False
      | Some x => occurs x t
    end.

  Fixpoint sort_insert(l: list nat): (tree) :=
    match l with
    | nil => leaf
    | cons x xs => insert x (sort_insert xs)
    end.

  Fixpoint to_list(t: tree): (list nat) :=
    match t with
    | leaf => []
    | node l v r => (to_list l) ++ v::to_list r
    end.

  Definition sort(t : tree) : tree :=
    sort_insert (to_list t).
  
  Fixpoint list_min(l: list nat) : option nat:=
    match l with
    | nil => None
    | cons x xs => match list_min xs with
      | None => Some x
      | Some y => Some (Nat.min x y)
      end
    end.
  
  Fixpoint treeMin(t: tree): option nat :=
    match t with
      | leaf => None
      | node l v r => 
        match (treeMin l, treeMin r) with
          | (None, None) => Some v
          | (None, Some y) => Some (Nat.min v y)
          | (Some x, None) => Some (Nat.min v x)
          | (Some x, Some y) => Some (Nat.min v (Nat.min x y))
        end
    end.
  Print treeMin.

  Fixpoint leftmost(t: tree): option nat :=
    match t with
    | leaf => None
    | node l v r => match leftmost l with
      | None => Some v
      | Some y => Some y
      end
    end.
  
  Fixpoint search(t: tree)(n: nat): Prop :=
    match t with
    | leaf => False
    | node l v r => match Nat.compare n v with
      | Lt => search l n
      | Eq => True
      | Gt => search r n
      end
    end.

End TypeAndFunctionDefinitions.

(*
Compute(insert 2 (node leaf 3 leaf)).
Compute(sort_insert [3;2;11]).
Compute(insert 2 (node leaf 3 leaf)).
Compute (treeMin (node (node leaf 11 leaf) 3 (node leaf 1 (node leaf 3 leaf)))).

Compute(search (node (node leaf 2 leaf) 5 (node (node leaf 7 leaf) 8 leaf)) 5).
Compute(search (node (node leaf 2 leaf) 5 (node (node leaf 7 leaf) 8 leaf)) 7).
Compute(search (node (node leaf 2 leaf) 5 (node (node leaf 7 leaf) 8 leaf)) 11).
Compute(search (node (node leaf 2 leaf) 5 (node (node leaf 7 leaf) 8 leaf)) 2).
*)

Section PartOneLemmas.

(* 
  This section contains:
  n <= n0 /\ all_leq n0 t -> all_leq n0 (insert n t)
  n > n0 /\ all_geq n0 t -> all_geq n0 (insert n t)
  bst t -> bst (insert n t)
  t1 = t2 -> insert a t1 = insert a t2
  insert a t1 = insert a t2 -> t1 = t2 ---Incomplete
  occurs a (insert a t)
  a = n \/ occurs n t -> occurs n (insert a t)
  occurs n (insert a t) -> a = n \/ occurs n t
  
*)
Section InsertLemmas.
  Lemma leq_insert: forall t: tree, forall n n0: nat,
    n <= n0 /\ all_leq n0 t -> all_leq n0 (insert n t).
  Proof.
  intros.
  destruct H.
  induction t.
  - simpl. auto.
  - simpl. simpl in H0.
    destruct H0 as [H1 [H2 H3]].
    destruct (n <=? n1) as []eqn:?.
    * simpl; auto.
    * simpl; auto.
  Qed.

  Lemma gr_insert: forall t: tree, forall n n0: nat,
    n > n0 /\ all_geq n0 t -> all_geq n0 (insert n t).
  Proof.
  intros.
  destruct H.
  induction t.
  - simpl. auto.
  - simpl. simpl in H0.
    destruct H0 as [H1 [H2 H3]].
    destruct (n <=? n1) as []eqn:?.
    * simpl; auto.
    * simpl; auto.
  Qed.

  Lemma insert_correctness: forall t: tree, forall n: nat, 
    bst t -> bst (insert n t).
  Proof.
  intros.
  induction t.
  * simpl; auto.
  * simpl; simpl in H.
    destruct H as [H1 [H2 [H3 H4]]].
    destruct (n <=? n0) as []eqn:?.
    - simpl.
      repeat split.
      apply leq_insert.
      split.
      apply leb_complete in Heqb.
      assumption.
      assumption. 
      assumption.
      apply IHt1; assumption.
      assumption.
    - simpl.
      apply leb_complete_conv in Heqb.
      repeat split.
      assumption.
      apply gr_insert.
      auto.
      assumption.
      apply IHt2; assumption.
  Defined.

  Lemma inserted_element_present: forall t: tree, forall a: nat,
    occurs a (insert a t).
  Proof.
  intros.
  induction t.
  - simpl. auto.
  - simpl.
    destruct (a <=? n).
    * simpl. right. left. assumption.
    * simpl. right. right. assumption.
  Defined.

  Lemma insert_retains_elements: forall t: tree, forall a n: nat,
     a = n \/ occurs n t -> occurs n (insert a t).
  Proof.
  intros.
  destruct H.
  - rewrite H.
    apply inserted_element_present.
  - induction t.
    * simpl in H. simpl. auto.
    * simpl.
      simpl in H.
      destruct H as [H1 | [H2 | H3]].
      + destruct (a <=? n0).
        simpl. auto.
        simpl. auto.
      + destruct (a <=? n0).
        simpl. auto.
        simpl. auto.
      + destruct (a <=? n0).
        simpl. auto.
        simpl. auto.
  Defined.

  Lemma insert_retains_elements_back: forall t: tree, forall a n: nat,
     occurs n (insert a t) -> a = n \/ occurs n t.
  Proof.
  intros.
  induction t.
  - simpl in H. destruct H as [H1|[H2|H3]]. auto. auto. auto.
  - simpl in H.
    destruct (a <=? n0).
    * simpl in H.
      simpl.
      destruct H as [H1|[H2|H3]].
      + auto.
      + apply or_comm. apply or_assoc. right. 
        apply or_assoc. apply or_comm. apply or_assoc. right.
        auto.
      + apply or_comm. apply or_assoc. right.
        apply or_assoc. right.
        auto.
    * simpl.
      simpl in H.
      destruct H as [H1|[H2|H3]].
      + auto.
      + apply or_comm. apply or_assoc. right.
        apply or_assoc. apply or_comm. apply or_assoc. right.
        auto.
      + apply or_comm. apply or_assoc. right.
        apply or_assoc. right.
        apply or_comm. auto.
  Defined.
End InsertLemmas.

(*
  This section contains:
  occurs x t -> In x (to_list t
  In x (to_list t) -> occurs x t
*)
Section ToListLemmas.
  Lemma to_list_retains_elements: forall t: tree, forall x: nat,
    occurs x t -> In x (to_list t).
  Proof.
  intros.
  induction t.
  - simpl. simpl in H. assumption.
  - simpl in H.
    destruct H.
    * rewrite H.
      simpl.
      apply in_elt.
    * destruct H.
      + simpl.
        apply in_or_app.
        left; apply IHt1; assumption.
      + simpl.
        apply in_or_app.
        right.
        apply in_cons.
        apply IHt2; assumption.
  Defined.

  Lemma to_list_retains_elements_back: forall t: tree, forall x: nat,
    In x (to_list t) -> occurs x t.
  Proof.
  intros.
  induction t.
  - auto.
  - simpl.
    simpl in H.
    apply in_app_or in H.
    simpl.
    destruct H as [H1|[H2|H3]].
    * auto.
    * left. auto.
    * right. right. auto.
  Defined.
End ToListLemmas.


(*
  This section contains:
  sort_insert (l1 ++ l2) t = sort_insert l1 (sort_insert l2 t)
  bst t -> bst (sort_insert l t)
  bst (sort t)

  In n l -> occurs n (sort_insert l leaf)
  occurs n (sort_insert l leaf) -> In n l
  occurs n t -> occurs n (sort t)
  occurs n (sort t) -> occurs n t
  occurs n t <-> occurs n (sort t)
*)
Section SortLemmas.

  
  Lemma sort_insert_is_bst: forall l: list nat,
    bst (sort_insert l).
  Proof.
  intros.
  induction l.
  - simpl. tauto.
  - simpl.
    apply insert_correctness.
    assumption.
  Defined.

  Lemma sort_result_is_bst: forall t: tree, bst (sort t).
  Proof.
  intros.
  unfold sort.
  induction t.
  - simpl. tauto.
  - apply sort_insert_is_bst.
  Qed.

  Lemma sort_insert_retention: forall n: nat, forall l: (list nat),
    In n l -> occurs n (sort_insert l).
  Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    simpl in H.
    destruct H.
    * apply insert_retains_elements.
      auto.
    * apply insert_retains_elements.
      right. auto.
  Defined.

  Lemma sort_insert_retention_back: forall n: nat, forall l: (list nat),
    occurs n (sort_insert l) -> In n l.
  Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    simpl in H.
    apply insert_retains_elements_back in H.
    destruct H.
    * auto.
    * right.
      auto.
  Defined.

  Lemma sort_retention_forward: forall n: nat, forall t: tree,
    occurs n t -> occurs n (sort t).
  Proof.
  intros.
  induction t.
  - simpl; simpl in H; assumption.
  - simpl in H.
    apply sort_insert_retention.
    destruct H as [H1 | [H2 | H3]].
    * simpl.
      apply in_or_app.
      right.
      rewrite H1.
      apply in_eq.
    * simpl.
      apply in_or_app.
      left.
      apply to_list_retains_elements.
      assumption.
    * simpl.
      apply in_or_app.
      right.
      apply in_cons.
      apply to_list_retains_elements.
      assumption.
  Defined.

  Lemma sort_retention_backward: forall n: nat, forall t: tree,
     occurs n (sort t) -> occurs n t.
  Proof.
  intros.
  induction t.
  - simpl; simpl in H; assumption.
  - simpl.
    apply sort_insert_retention_back in H.
    simpl in H.
    apply in_app_or in H.
    simpl in H.
    destruct H as [H1 | [H2|H3]].
    * right;left.
      apply to_list_retains_elements_back.
      auto.
    * auto.
    * right; right.
      apply to_list_retains_elements_back.
      auto.
  Defined.

  Lemma sort_retention: forall n: nat, forall t: tree,
    occurs n t <-> occurs n (sort t).
  Proof.
  intros.
  split.
  apply sort_retention_forward.
  apply sort_retention_backward.
  Qed.

End SortLemmas.

End PartOneLemmas.

Section PartTwoLemmas.

Lemma min_element_in_tree: forall t: tree,
  treeMin t <> None -> occurs_opt (treeMin t) t.
Proof.
intros.
Qed.
End PartTwoLemmas.