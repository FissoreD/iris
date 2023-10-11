From iris.algebra Require Import gset.

Lemma test_op (X Y : gset nat) : X ⊆ Y → X ⋅ Y = Y.
Proof. set_solver. Qed.
Lemma test_included (X Y : gset nat) : X ≼ Y → X ∪ Y = Y ∧ X ∩ Y = X.
Proof. set_solver. Qed.

Lemma test_disj_included (X Y : gset nat) : GSet X ≼ GSet Y → X ∪ Y = Y ∧ X ∩ Y = X.
Proof. set_solver. Qed.
Lemma test_disj_equiv n : GSet (∅ : gset nat) ≡ GSet {[n]} → False.
Proof. set_solver. Qed.
Lemma test_disj_eq n : GSet (∅ : gset nat) = GSet {[n]} → False.
Proof. set_solver. Qed.
Lemma test_disj_valid (X Y : gset nat) : ✓ (GSet X ⋅ GSet Y) → X ∩ Y = ∅.
Proof. set_solver. Qed.


(** Below lemmas test [IsOp] inference on [gset]s.
Expected behavior for simplifying [op]s is:
  - X ⋅ ∅ ~~> X
  - X ⋅ X ~~> X
  - X ⋅ Y ~~> X ∪ Y
Expected behavior when requested to 'introduce' [op]s is:
  - X ∪ Y ~~> X ⋅ Y
  - X ~~> X ⋅ ∅ *)
Lemma test_isop (X Y Z : gset nat) (H : Z ∪ Y = X) : X ⋅ ∅ ≡ Y ∪ Z.
Proof.
  rewrite -(proofmode_classes.is_op _ X ∅). (* X ⋅ ∅ ~~> X *)
  rewrite {1}(proofmode_classes.is_op X). (* X ~~> X ⋅ X *)
  rewrite -(proofmode_classes.is_op _ X X). (* X ⋅ X ~~> X *)
  rewrite (proofmode_classes.is_op (Y ∪ Z)). (* Y ∪ Z ~~> Y ⋅ Z *)
  rewrite -(proofmode_classes.is_op _ Y Z). (* Y ⋅ Z ~~> Y ∪ Z *)
  set_solver.
Qed.
