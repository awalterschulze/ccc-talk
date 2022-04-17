Require Import Coq.Arith.PeanoNat.

(* hide so that we don't have to explain notations *)
Infix "<" := Nat.ltb.
Infix "<=" := Nat.leb.
Notation "a == b" := (Nat.eqb a b) (at level 70).
Notation "x + 1" := (S x) (at level 70).
Tactic Notation "induction_on_tree" constr(T) :=
  induction T as [| lefty IHlefty tvalue righty IHrighty].
Tactic Notation "induction_on_bst" constr(B) :=
  induction B as [| l bvalue r leftIsLess rightIsMore BSTl IHL BSTr IHR].
Ltac split3 := split; [| split].
Ltac evaluate := repeat (simpl || rewrite Nat.ltb_irrefl || rewrite Nat.eqb_refl); try reflexivity.

(* hide so that we  don't have to explain ltac *)
Ltac case_cmp x y C :=
  remember (Nat.compare x y) as C;
  match goal with
  | [ C: comparison |- _ ] =>
    induction C
  end;
  match goal with
  | [ H : Eq = _ |- _ ] =>
    rename H into C;
    symmetry in C;
    apply Nat.compare_eq in C;
    rewrite C
  | [ H : Lt = _ |- _ ] =>
    rename H into C;
    symmetry in C;
    rewrite Nat.compare_lt_iff in C;
    rewrite <- Nat.ltb_lt in C
  | [ H : Gt = _ |- _ ] =>
    rename H into C;
    symmetry in C;
    rewrite Nat.compare_gt_iff in C;
    rewrite <- Nat.ltb_lt in C
  end.

Tactic Notation "compare" constr(X) constr(Y) "as" ident(C) :=
  case_cmp X Y C.

(* hide so that we don't have to explain Prop *)
Lemma ltb_ge:
  forall x y : nat, (x < y) = false <-> (y <= x) = true.
Proof.
intros.
split; intros.
- apply Nat.ltb_ge in H.
  rewrite Nat.leb_le.
  assumption.
- apply Nat.ltb_ge.
  rewrite Nat.leb_le in H.
  assumption.
Qed.

(* hide so that we don't have to explain Prop *)
Lemma le_neq:
  forall x y: nat, (x < y = true) <-> (x <= y = true) /\ x == y = false.
Proof.
intros.
split; intros.
- rewrite Nat.leb_le.
  rewrite Nat.eqb_neq.
  rewrite Nat.ltb_lt in H.
  apply Nat.le_neq.
  assumption.
- rewrite Nat.leb_le in H.
  rewrite Nat.eqb_neq in H.
  rewrite Nat.ltb_lt.
  apply Nat.le_neq.
  assumption.
Qed.

(* a basic proofs of lt *)
Lemma Lt_implies_Leq:
  forall (x: nat) (y: nat),
  (x < y = true) -> (x <= y = true).
Proof.
intros.
Search (?X < ?Y = true).
apply le_neq in H.
destruct H.
exact H.
Qed.

(* a basic proofs of lt *)
Lemma Lt_implies_not_Lt:
  forall {x: nat} {y: nat},
  (x < y) = true
  -> y < x = false.
Proof.
intros.
compare x y as C.
- SearchRewrite (?X < ?X).
  rewrite Nat.ltb_irrefl.
  reflexivity.
- Search (?X < ?Y = false).
  apply ltb_ge.
  apply Lt_implies_Leq.
  assumption.
- rewrite ltb_ge.
  apply Lt_implies_Leq.
  assumption.
Qed.

(* Show side by side Kotlin implementation *)
Inductive tree : Type :=
| Nil
| Node (lefty : tree) (value : nat) (righty : tree).

Fixpoint contains (x : nat) (t : tree) : bool :=
  match t with
  | Nil => false
  | Node l y r =>
    if x < y
    then contains x l
    else
      if y < x
      then contains x r
      else x == y
  end.

Example ex_tree_1 :=
  Node Nil 1 Nil.

Theorem Contains1:
  contains 1 ex_tree_1 = true.
Proof.
evaluate.
Qed.

Theorem ContainsNested1:
  forall (t: tree), t = Node ex_tree_1 2 (Node Nil 3 Nil) -> contains 1 t = true.
Proof.
intros.
destruct t.
- discriminate.
- injection H.
  intros Ht2 Hv Ht1.
  rewrite Hv.
  evaluate.
  rewrite Ht1.
  apply Contains1.
Qed.

Fixpoint insert (value : nat) (t : tree) : tree :=
  match t with
  | Nil => Node Nil value Nil
  | Node l tvalue r =>
    if value < tvalue
    then Node (insert value l) tvalue r
    else
      if tvalue < value
      then Node l tvalue (insert tvalue r)
      else Node l value r
  end.

Theorem contains_insert_eq : forall (t : tree) (value: nat),
  contains value (insert value t) = true.
Proof.
intros.
induction_on_tree t.
- evaluate.
- evaluate.
  compare value tvalue as C.
  + evaluate.
  + rewrite C.
    evaluate.
    rewrite C.
    exact IHlefty.
  + rewrite C.
    specialize (Lt_implies_not_Lt C) as C'.
    rewrite C'.
    evaluate.
    rewrite C'.
    rewrite C.
    Fail assumption.
Abort.

Fixpoint bst_insert (value: nat) (t : tree) : tree :=
  match t with
  | Nil => Node Nil value Nil
  | Node l bvalue r =>
    if value < bvalue
    then Node (bst_insert value l) bvalue r
    else
      if bvalue < value
      then Node l bvalue (bst_insert value r)
      else Node l value r
  end.

Theorem lookup_bst_insert_eq:
  forall (t : tree) (ivalue: nat),
  contains ivalue (bst_insert ivalue t) = true.
Proof.
intros.
induction_on_tree t.
- evaluate.
- evaluate.
  compare ivalue tvalue as C.
  + evaluate.
  + rewrite C.
    evaluate.
    rewrite C.
    exact IHlefty.
  + specialize (Lt_implies_not_Lt C) as C'.
    rewrite C'.
    rewrite C.
    evaluate.
    rewrite C'.
    rewrite C.
    exact IHrighty.
Qed.

Fixpoint AllLess (t: tree) (parent: nat) :=
  match t with
  | Nil => True
  | Node l v r =>
    (v < parent = true) /\ AllLess l parent /\ AllLess r parent
  end.

Theorem all_less:
  forall {ivalue: nat} {t: tree} {bvalue: nat}
  (AL: AllLess t bvalue)
  (BIC: (ivalue < bvalue) = true),
  AllLess (bst_insert ivalue t) bvalue.
Proof.
intros.
induction_on_tree t.
- evaluate.
  split3; easy.
- evaluate.
  destruct AL as [BTC All].
  destruct All as [AllLefty AllRighty].
  specialize (IHlefty AllLefty) as IHlefty.
  specialize (IHrighty AllRighty) as IHrighty.
  compare ivalue tvalue as ITC.
  + evaluate.
    split3.
    * rewrite ITC in BIC. exact BIC.
    * exact AllLefty.
    * exact AllRighty.
  + rewrite ITC.
    evaluate.
    split3.
    * exact BTC.
    * exact IHlefty.
    * exact AllRighty.
  + rewrite ITC.
    specialize (Lt_implies_not_Lt ITC) as TIC.
    rewrite TIC.
    evaluate.
    split3.
    * exact BTC.
    * exact AllLefty.
    * apply IHrighty.
Qed.

Fixpoint AllMore (t: tree) (parent: nat) :=
  match t with
  | Nil => True
  | Node l v r =>
    (parent < v = true) /\ AllMore l parent /\ AllMore r parent
  end.

Theorem all_more:
  forall {ivalue: nat} {t: tree} {bvalue: nat}
  (AL: AllMore t bvalue)
  (BIC: (bvalue < ivalue) = true),
  AllMore (bst_insert ivalue t) bvalue.
Proof.
intros.
induction_on_tree t.
- evaluate.
  split3; easy.
- evaluate.
  destruct AL as [BTC All].
  destruct All as [AllLefty AllRighty].
  specialize (IHlefty AllLefty) as IHlefty.
  specialize (IHrighty AllRighty) as IHrighty.
  compare ivalue tvalue as ITC.
  + evaluate.
    split3.
    * rewrite ITC in BIC. exact BIC.
    * exact AllLefty.
    * exact AllRighty.
  + rewrite ITC.
    evaluate.
    split3.
    * exact BTC.
    * exact IHlefty.
    * exact AllRighty.
  + rewrite ITC.
    specialize (Lt_implies_not_Lt ITC) as TIC.
    rewrite TIC.
    evaluate.
    split3.
    * exact BTC.
    * exact AllLefty.
    * apply IHrighty.
Qed.

Inductive BST : tree -> Prop :=
  | BST_Nil : BST Nil
  | BST_Node : forall l x r,
    AllLess l x ->
    AllMore r x ->
    BST l ->
    BST r ->
    BST (Node l x r).

(* Example is_BST_ex :
    BST ex_tree. *)

(* Example not_BST_ex :
    ¬ BST NotBst.t. *)

(* Gaurantees that it is correctly constructed: title of the talk *)

Theorem insert_BST : forall (t : tree) (B: BST t) (ivalue : nat),
  BST (bst_insert ivalue t).
Proof.
intros t B.
induction_on_bst B.
- intros.
  evaluate.
  constructor.
  + easy.
  + easy.
  + constructor.
  + constructor.
- intros.
  evaluate.
  compare ivalue bvalue as IBC.
  + evaluate.
    constructor.
    * exact leftIsLess.
    * exact rightIsMore.
    * exact BSTl.
    * exact BSTr.
  + rewrite IBC.
    constructor.
    * exact (all_less leftIsLess IBC).
    * exact rightIsMore.
    * apply IHL.
    * exact BSTr.
  + rewrite IBC.
    rewrite (Lt_implies_not_Lt IBC).
    constructor.
    * exact leftIsLess.
    * exact (all_more rightIsMore IBC).
    * exact BSTl.
    * apply IHR.
Qed.
