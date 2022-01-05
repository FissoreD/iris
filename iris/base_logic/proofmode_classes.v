From iris.algebra Require Import cmra.
From iris.base_logic Require Import own.
From iris.proofmode Require Import proofmode.

Class IsValidOp {A : cmra} (a a1 a2 : A) M (P : uPred M) := {
  is_valid_merge : ✓ (a1 ⋅ a2) ⊢ □ P ;
  is_valid_op : ✓ (a1 ⋅ a2) ⊢@{uPredI M} a ≡ a1 ⋅ a2 ;
}.

Global Hint Mode IsValidOp ! - ! ! ! - : typeclass_instances.

Definition includedI {M : ucmra} {A : cmra} (a b : A) : uPred M
  := (∃ c, b ≡ a ⋅ c)%I.

Notation "a ≼ b" := (includedI a b) : bi_scope.

Class IsIncludedMerge {A : cmra} (a1 a2 : A) M (P : uPred M) := 
  is_included_merge : ✓ a2 ⊢ a1 ≼ a2 ∗-∗ □ P.

Global Hint Mode IsIncludedMerge ! ! ! ! - : typeclass_instances.

Class HasRightId {A : cmra} (a : A) :=
  has_right_id : a ≼ a.

Global Hint Mode HasRightId ! ! : typeclass_instances.

Class IsIncludedMergeUnital {A : cmra} (a1 a2 : A) M (P_lt P_le : uPred M) := {
  included_merge_from_unital : IsIncludedMerge a1 a2 M P_lt;
  is_included_merge_unital : ✓ a2 ⊢ (□ P_lt ∨ a1 ≡ a2) ∗-∗ □ P_le;
}.

Global Hint Mode IsIncludedMergeUnital ! ! ! ! - - : typeclass_instances.


Section proper.
  Global Instance includedI_proper_1 {M : ucmra} {A : cmra} : 
    NonExpansive2 (includedI (M := M) (A := A)).
  Proof. solve_proper. Qed.
  Global Instance includedI_proper_2 {M : ucmra} {A : cmra} : 
    Proper ((≡) ==> (≡) ==> (≡)) (includedI (M := M) (A := A)).
  Proof. solve_proper. Qed.

  Global Instance is_valid_op_proper {A : cmra} :
    Proper ((≡) ==> (≡) ==> (≡) ==> forall_relation (λ M, (⊣⊢@{uPredI M}) ==> (iff))) (IsValidOp (A := A)).
  Proof.
    move => a1 a1' Ha1 a2 a2' Ha2 a a' Ha M P2 P2' HP2.
    split; case => H1 H2; split.
    - rewrite -HP2 -Ha -Ha2 //.
    - rewrite -Ha2 -Ha -Ha1 //.
    - rewrite HP2 Ha Ha2 //.
    - rewrite Ha2 Ha Ha1 //.
  Qed.

  Global Instance merge_proper {A : cmra} : 
    Proper ((≡) ==> (≡) ==> forall_relation (λ M, (⊣⊢@{uPredI M}) ==> (iff))) 
      (IsIncludedMerge (A := A)).
  Proof. solve_proper. Qed.

  Global Instance merge_unital_proper {A : cmra} : 
    Proper ((≡) ==> (≡) ==> 
        forall_relation (λ M, (⊣⊢@{uPredI M}) ==> (⊣⊢@{uPredI M}) ==> (iff))) 
      (IsIncludedMergeUnital (A := A)).
  Proof.
    move => a1 a1' Ha1 a2 a2' Ha2 Σ P1 P1' HP1 P2 P2' HP2.
    split; case => H1 H2; split.
    - revert H1; apply merge_proper => //.
    - rewrite -Ha2 H2 HP1 Ha1 HP2 //.
    - revert H1; apply merge_proper => //.
    - rewrite Ha2 H2 HP1 Ha1 HP2 //.
  Qed.
End proper.