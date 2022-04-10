Require Import Coq.Arith.PeanoNat.

Infix "<" := Nat.ltb.
Notation "a == b" := (Nat.eqb a b) (at level 70).
(* Notation "a > b" := (Nat.ltb b a) (at level 70). *)
Notation "x + 1" := (S x) (at level 70).

(* some basic proofs of lt *)

Ltac case_lt x y :=
  remember (Nat.compare x y) as C;
  match goal with
  | [ C: comparison |- _ ] =>
    induction C
  end;
  let C := fresh "C" in
  match goal with
  | [ H : Eq = _ |- _ ] =>
    rename H into C;
    symmetry in C;
    apply Nat.compare_eq in C
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

Lemma Leq:
  forall (x: nat) (y: nat),
  (x < y = true) -> x <= y.
Proof.
intros.
rewrite Nat.ltb_lt in H.
rewrite Nat.le_neq in H.
destruct H.
assumption.
Qed.

Lemma Lt:
  forall (x: nat) (y: nat),
  (x < y) = true
  -> y < x = false.
Proof.
intros.
case_lt x y.
- rewrite C.
  SearchRewrite (?X < ?X).
  rewrite Nat.ltb_irrefl.
  reflexivity.
- Search (?X < ?Y = false).
  rewrite Nat.ltb_ge.
  apply Leq.
  assumption.
- rewrite Nat.ltb_ge.
  apply Leq.
  assumption.
Qed.

Lemma Eq:
forall (x: nat) (y: nat),
  (y < x) = false -> (x < y) = false -> x = y.
Proof.
intros.
case_lt x y.
- assumption.
- rewrite H0 in C.
  discriminate.
- rewrite H in C.
  discriminate.
Qed.

(* Show side by side Kotlin implementation *)
Inductive tree : Type :=
| Nil
| Node (lefty : tree) (value : nat) (righty : tree).
(* left loosey *)
(* righty tighty *)

(*
Inductive Contains: nat -> tree -> Prop :=
| Inside: forall (x: nat) (y: nat) (l: tree) (r: tree),
  x = y \/ Contains x l \/ Contains x r ->
  Contains x (Node l x r). *)

(* Kotlin
sealed class Tree {
    object Nil : Tree() {}

    data class Node(
        val value: Int,
        val lefty: Tree = Nil,
        val righty: Tree = Nil
    ) : Tree()
}
*)

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

(* Have kotlin code for contains or insert

https://proandroiddev.com/algebraic-data-types-in-kotlin-337f22ef230a

fun Tree<Int>.sum(): Long = when (this) {
    Empty -> 0
    is Node -> value + left.sum() + right.sum()
}

Node(value=42, left=Empty, right=Node(value=62, left=Empty, right=Empty))
*)

Example ex_tree_1 :=
  Node Nil 1 Nil.

Theorem Example1:
  contains 1 ex_tree_1 = true.
Proof.
simpl.
reflexivity.
Qed.

Theorem Example2:
  forall (t: tree), t = Node ex_tree_1 2 (Node Nil 3 Nil) -> contains 1 t = true.
Proof.
intros.
destruct t.
- discriminate.
- injection H.
  intros Ht2 Hv Ht1.
  rewrite Hv.
  simpl.
  rewrite Ht1.
  apply Example1.
Qed.

Fixpoint insert (x : nat) (t : tree) : tree :=
  match t with
  | Nil => Node Nil x Nil
  | Node l y r =>
      if x < y
      then Node (insert x l) y r
      else
        if y < x
        then Node l y (insert y r)
        else Node l x r
  end.

Theorem lookup_insert_eq : forall (t : tree) (x: nat),
  contains x (insert x t) = true.
Proof.
intros.
induction t.
- simpl.
  SearchRewrite (?X < ?X).
  rewrite Nat.ltb_irrefl.
  SearchRewrite (?X == ?X).
  rewrite Nat.eqb_refl.
  reflexivity.
- (* is there a way to set default names for t1, t2 and value *)
  simpl.
  case_lt x value.
  + rewrite <- C.
    SearchRewrite (?X < ?X).
    rewrite Nat.ltb_irrefl.
    simpl.
    rewrite Nat.ltb_irrefl.
    SearchRewrite (?X == ?X).
    rewrite Nat.eqb_refl.
    reflexivity.
  + rewrite C.
    simpl.
    rewrite C.
    exact IHt1.
  + rewrite C.
    specialize (Lt _ _ C) as C0.
    rewrite C0.
    simpl.
    rewrite C0.
    rewrite C.
    Fail assumption.
Abort.

Fixpoint bst_insert (x : nat) (t : tree) : tree :=
  match t with
  | Nil => Node Nil x Nil
  | Node l y r => if x < y then Node (bst_insert x l) y r
                 else if y < x then Node l y (bst_insert x r)
                      else Node l x r
  end.

Theorem lookup_bst_insert_eq : forall (t : tree) (x: nat),
  contains x (bst_insert x t) = true.
Proof.
intros.
induction t.
- simpl.
  SearchRewrite (?X < ?X).
  rewrite Nat.ltb_irrefl.
  SearchRewrite (?X == ?X).
  rewrite Nat.eqb_refl.
  reflexivity.
- (* is there a way to set default names for t1, t2 and value *)
  simpl.
  case_lt x value.
  + rewrite C.
    rewrite Nat.ltb_irrefl.
    simpl.
    rewrite Nat.ltb_irrefl.
    rewrite Nat.eqb_refl.
    reflexivity.
  + rewrite C.
    simpl.
    rewrite C.
    exact IHt1.
  + specialize (Lt _ _ C) as C0.
    rewrite C0.
    rewrite C.
    simpl.
    rewrite C0.
    rewrite C.
    exact IHt2.
Qed.

Fixpoint AllChildren (P: nat -> Prop) (t: tree) : Prop :=
  match t with
  | Nil => True
  | Node l x r => P x /\ AllChildren P l /\ AllChildren P r
  end.

  (* Why is not this not LogN when insert is? *)
Inductive BST : tree -> Prop :=
| BST_Nil : BST Nil
| BST_Node : forall l x r,
    AllChildren (fun y => y < x = true) l ->
    AllChildren (fun y => x < y = true) r ->
    BST l ->
    BST r ->
    BST (Node l x r).

Print Nat.leb.

(* Example is_BST_ex :
    BST ex_tree. *)

(* Example not_BST_ex :
    ¬ BST NotBst.t. *)

Lemma AllChildren_insert : forall (P : nat -> Prop) (t : tree),
    AllChildren P t -> forall (x : nat), P x -> AllChildren P (bst_insert x t).
Proof.
induction t; intros.
- simpl.
  split.
  + assumption.
  + split.
    * apply I.
    * exact I.
- simpl.
  case_lt x value.
  + rewrite C.
    rewrite Nat.ltb_irrefl.
    assumption.
  + rewrite C.
    destruct H.
    destruct H1.
    simpl.
    split.
    * assumption.
    * split.
      --- apply IHt1.
          +++ exact H1.
          +++ exact H0.
      --- exact H2.
  + specialize (Lt _ _ C) as C0.
    rewrite C0.
    rewrite C.
    destruct H.
    destruct H1.
    simpl.
    split.
    * assumption.
    * split.
      --- exact H1.
      --- apply IHt2.
          +++ exact H2.
          +++ exact H0.
Qed.

(* Gaurantees that it is correctly constructed: title of the talk *)

Theorem insert_BST : forall (x : nat) (t : tree),
    BST t -> BST (bst_insert x t).
Proof.
intros.
generalize dependent x.
induction H.
- intros.
  simpl.
  apply BST_Node.
  + cbn. apply I.
  + cbn. apply I.
  + apply BST_Nil.
  + apply BST_Nil.
- intros.
  simpl.
  case_lt x0 x.
  + rewrite C.
    rewrite Nat.ltb_irrefl.
    apply BST_Node.
    * exact H.
    * exact H0.
    * exact H1.
    * exact H2.
  + rewrite C.
    apply BST_Node.
    * apply AllChildren_insert.
      --- exact H.
      --- exact C.
    * apply H0.
    * apply IHBST1.
    * apply H2.
  + specialize (Lt _ _ C) as C0.
    rewrite C0.
    rewrite C.
    apply BST_Node.
    * exact H.
    * apply AllChildren_insert.
      --- exact H0.
      --- exact C.
    * exact H1.
    * apply IHBST2.
Qed.
