Require Import Coq.Arith.PeanoNat.
Require Import Cmp.

Infix "<" := Nat.ltb.
Notation "a == b" := (Nat.eqb a b) (at level 70).
Notation "a > b" := (Nat.ltb b a) (at level 70).
Notation "x + 1" := (S x) (at level 70).

(* some basic proofs of lt *)

Check Nat.ltb_irrefl.

(* we construct that two numbers are always leb *)
(* is this too much of a diversion? *)
(* Inductive Leb : nat -> nat -> Prop :=
| Same : forall (x: nat), Leb x x
| Succ : forall (x: nat) (y: nat),
    Leb x y -> Leb x (y + 1). *)
(* constructing correct leb *)
(* why is this useful *)
(* lets look at a more complicated example, BST *)


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
        if x > y
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
        if x > y
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
  remember (value > x) as Hgt.
  remember (value < x) as Hlt.
  case Hgt, Hlt.
  + simpl.
    rewrite <- HeqHgt.
    exact IHt1.
  + simpl.
    rewrite <- HeqHgt.
    exact IHt1.
  + simpl.
    rewrite <- HeqHgt.
    rewrite <- HeqHlt.
    Fail assumption.
Abort.

Fixpoint good_insert (x : nat) (t : tree) : tree :=
  match t with
  | Nil => Node Nil x Nil
  | Node l y r => if x < y then Node (good_insert x l) y r
                 else if x > y then Node l y (good_insert x r)
                      else Node l x r
  end.

Theorem lookup_good_insert_eq : forall (t : tree) (x: nat),
  contains x (good_insert x t) = true.
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
  remember (value > x) as Hgt.
  remember (value < x) as Hlt.
  case Hgt, Hlt.
  + simpl.
    rewrite <- HeqHgt.
    exact IHt1.
  + simpl.
    rewrite <- HeqHgt.
    exact IHt1.
  + simpl.
    rewrite <- HeqHgt.
    rewrite <- HeqHlt.
    exact IHt2.
  + simpl.
    rewrite Nat.ltb_irrefl.
    rewrite Nat.eqb_refl.
    reflexivity.
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
    AllChildren (fun y => y > x = true) r ->
    BST l ->
    BST r ->
    BST (Node l x r).

Print Nat.leb.

(* Example is_BST_ex :
    BST ex_tree. *)

(* Example not_BST_ex :
    ¬ BST NotBst.t. *)

Lemma AllChildren_insert : forall (P : nat -> Prop) (t : tree),
    AllChildren P t -> forall (x : nat),
      P x -> AllChildren P (insert x t).
Admitted.

(* Gaurantees that it is correctly constructed: title of the talk *)

Theorem insert_BST : forall (x : nat) (t : tree),
    BST t -> BST (insert x t).
Proof.
  (* FILL IN HERE *) Admitted.
