From iris.algebra Require Import cmra.
From iris.base_logic Require Import own.
From iris.proofmode Require Import proofmode.

Class IsValidOp {A : cmra} M (a a1 a2 : A) (P : uPred M) := {
  is_valid_merge : ✓ (a1 ⋅ a2) ⊢ □ P ;
  is_valid_op : ✓ (a1 ⋅ a2) ⊢@{uPredI M} a ≡ a1 ⋅ a2 ;
}.

Global Hint Mode IsValidOp ! ! - ! ! - : typeclass_instances.

Definition includedI {M : ucmra} {A : cmra} (a b : A) : uPred M
  := (∃ c, b ≡ a ⋅ c)%I.

Notation "a ≼ b" := (includedI a b) : bi_scope.

Class IsIncluded {A : cmra} M (a1 a2 : A) (P : uPred M) := 
  is_included_merge : ✓ a2 ⊢ a1 ≼ a2 ∗-∗ □ P.

Global Hint Mode IsIncluded ! ! ! ! - : typeclass_instances.

(* this is weaker than having a unit! Consider min_natR, agreeR *)
Class HasRightId {A : cmra} (a : A) :=
  has_right_id : a ≼ a.

Global Hint Mode HasRightId ! ! : typeclass_instances.

Class IsIncludedOrEq {A : cmra} M (a1 a2 : A) (P_lt P_le : uPred M) := {
  is_included_or_included : IsIncluded M a1 a2 P_lt;
  is_included_or_eq_merge : ✓ a2 ⊢ (□ P_lt ∨ a1 ≡ a2) ∗-∗ □ P_le;
}.

Global Hint Mode IsIncludedOrEq ! ! ! ! - - : typeclass_instances.


Section proper.
  Context {M : ucmra} {A : cmra}.
  Implicit Types a : A.

  Global Instance includedI_proper_1 : 
    NonExpansive2 (includedI (M := M) (A := A)).
  Proof. solve_proper. Qed.
  Global Instance includedI_proper_2 : 
    Proper ((≡) ==> (≡) ==> (≡)) (includedI (M := M) (A := A)).
  Proof. solve_proper. Qed.

  Global Instance is_valid_op_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (=) ==> (iff)) (IsValidOp (A := A) M).
  Proof.
    move => a1 a1' Ha1 a2 a2' Ha2 a a' Ha P2' P2 ->.
    split; case => H1 H2; split.
    - rewrite -Ha -Ha2 //.
    - rewrite -Ha -Ha2 -Ha1 //.
    - rewrite Ha Ha2 //.
    - rewrite Ha2 Ha Ha1 //.
  Qed.
  Lemma is_valid_op_weaken a a1 a2 P1 P2 :
    IsValidOp M a a1 a2 P1 →
    (✓ (a1 ⋅ a2) ∗ □ P1 ⊢ P2) →
    IsValidOp M a a1 a2 P2.
  Proof.
    case => HP Ha HP1P2; split; last done.
    iIntros "#H✓".
    rewrite -HP1P2.
    iFrame "#". by rewrite -HP.
  Qed.

  Global Instance is_included_proper : 
    Proper ((≡) ==> (≡) ==> (≡) ==> (iff)) (IsIncluded (A := A) M).
  Proof. solve_proper. Qed.
  Lemma is_included_weaken a1 a2 P1 P2 :
    IsIncluded M a1 a2 P1 →
    (✓ a2 ⊢ □ P1 ∗-∗ □ P2) →
    IsIncluded M a1 a2 P2.
  Proof.
    rewrite /IsIncluded => HP1a HP1P2.
    iIntros "#H✓". iApply bi.wand_iff_trans.
    - by iApply HP1a.
    - by iApply HP1P2.
  Qed.

  Global Instance is_included_or_eq_proper : 
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (iff)) (IsIncludedOrEq (A := A) M).
  Proof.
    move => a1 a1' Ha1 a2 a2' Ha2 P1' P1 HP1 P2' P2 HP2.
    split; case => H1 H2; split.
    - revert H1; apply is_included_proper => //.
    - rewrite -Ha2 -Ha1 -HP1 -HP2 //.
    - revert H1; apply is_included_proper => //.
    - rewrite Ha2 Ha1 HP1 HP2 //.
  Qed.
  Lemma is_included_or_eq_weaken a1 a2 P1 P2 P3 P4 :
    IsIncludedOrEq M a1 a2 P1 P2 →
    (✓ a2 ⊢ □ P1 ∗-∗ □ P3) →
    (✓ a2 ⊢ □ P2 ∗-∗ □ P4) →
    IsIncludedOrEq M a1 a2 P3 P4.
  Proof.
    case => HP1 HP1P2 HP1P3 HP2P4; split; first by eapply is_included_weaken.
    iIntros "#H✓". 
    iApply bi.wand_iff_trans; last by iApply HP2P4.
    iApply bi.wand_iff_trans; last by iApply HP1P2.
    iSplit; iIntros "[#HP|$]"; iLeft; by iApply HP1P3.
  Qed.
End proper.