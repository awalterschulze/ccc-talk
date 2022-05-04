Require Import ConstructionToolbox.

Lemma Lt_implies_Leq:
  forall {x: nat} {y: nat},
  (x < y = true) -> (x <= y = true).
Proof.
nail.
Search (?X < ?Y = true).
call (le_neq H) as H'.
wreck H' into Leq and Eq.
just Leq.
Qed.

(* START HERE *)

Lemma Lt_implies_not_Lt:
  forall {x: nat} {y: nat},
  (x < y) = true
  -> y < x = false.
Proof.
nail.
compare x y as C.
- (* Let's focus on case 1, where x = y *)
  SearchRewrite (?X < ?X).
  sub Nat.ltb_irrefl.
  same.
- (* Now let's focus on case 2, where x < y *)
  (* Earlier I proved ltb_ge: (y <= x) = true -> (x < y) = false *)
  apply ltb_ge.
  (* Now we can apply the theorem we proved before *)
  (* (x < y = true) -> (x <= y = true) *)
  apply Lt_implies_Leq.
  just C.
- apply ltb_ge.
  apply Lt_implies_Leq.
  just H.
Qed.