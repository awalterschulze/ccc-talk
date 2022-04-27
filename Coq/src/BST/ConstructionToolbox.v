Require Export Coq.Arith.PeanoNat.

(* hide so that we don't have to explain notations *)
Infix "<" := Nat.ltb.
Infix "<=" := Nat.leb.
Notation "a == b" := (Nat.eqb a b) (at level 70).
Notation "x + 1" := (S x) (at level 70).

Tactic Notation "induction_on_tree" constr(T) :=
  induction T as [| lefty IHlefty tvalue righty IHrighty].
Tactic Notation "induction_on_is_bst" constr(B) :=
  induction B as [| l bvalue r leftIsLess rightIsMore isBSTl IHlefty isBSTr IHrighty].
Ltac split3 := split; [| split].

Tactic Notation "nail" := intros.
Tactic Notation "nail" ident(H1) ident(H2) := intros H1 H2.
Tactic Notation "nail" ident(H1) ident(H2) ident(H3) := intros H1 H2 H3.
Tactic Notation "wreck" :=  constructor.
Tactic Notation "wreck" constr(H) :=  destruct H.
Tactic Notation "wreck" constr(H) "into" ident(H1) "and" ident(H2) := destruct H as [H1 H2].
Tactic Notation "wreck" constr(H) "into" ident(H1) "," ident(H2) "and" ident(H3) := injection H; intros H3 H2 H1.
Tactic Notation "just" constr(H) := exact H.
Tactic Notation "same" := reflexivity.
Tactic Notation "wat" := discriminate.
Tactic Notation "call" constr(B) "as" ident(A) :=
  specialize B as A.
Tactic Notation "sub" constr(A) :=
  rewrite A.
Tactic Notation "unapply" constr(A) := apply A.

Ltac evaluate := repeat (simpl || rewrite Nat.ltb_irrefl || rewrite Nat.eqb_refl).

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
  forall {x: nat} {y: nat}, (y <= x) = true -> (x < y) = false.
Proof.
nail.
apply Nat.ltb_ge.
rewrite Nat.leb_le in H.
assumption.
Qed.

(* hide so that we don't have to explain Prop *)
Lemma le_neq:
  forall {x: nat} {y: nat}, (x < y = true) -> (x <= y = true) /\ x == y = false.
Proof.
nail.
rewrite Nat.leb_le.
rewrite Nat.eqb_neq.
rewrite Nat.ltb_lt in H.
apply Nat.le_neq.
assumption.
Qed.