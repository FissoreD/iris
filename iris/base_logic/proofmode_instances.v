From iris.algebra Require Import cmra proofmode_classes.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import own proofmode_classes.

Set Default Proof Using "Type".


Global Instance includedI_into_pure `{CmraDiscrete A} (a b : A) {M} : 
  IntoPure (PROP := uPredI M) (a ≼ b)%I (a ≼ b).
Proof.
  rewrite /IntoPure. iDestruct 1 as (c) "%"; iPureIntro.
  by eexists.
Qed.


Section cmra_instances.
  Context {A : cmra} {M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  Lemma from_isop a a1 a2 :
    IsOp a a1 a2 → IsValidOp M a a1 a2 True.
  Proof. rewrite /IsOp; split; [ | rewrite H]; eauto. Qed.

  Lemma is_valid_op_comm a a1 a2 P :
    IsValidOp M a a1 a2 P → IsValidOp M a a2 a1 P.
  Proof. case; split; rewrite comm //. Qed.

  Lemma is_included_merge' a1 a2 P :
    IsIncludedMerge M a1 a2 P →
    a1 ≼ a2 ⊢ ✓ a2 -∗ □ P.
  Proof.
    rewrite /IsIncludedMerge => ->.
    iIntros "Ha1 HP".
    by iApply "HP".
  Qed.

  Global Instance unital_from_right_id a1 a2 P :
    HasRightId a2 →
    IsIncludedMerge M a1 a2 P →
    IsIncludedMergeUnital M a1 a2 P P | 100.
  Proof.
    rewrite /IsIncludedMerge => [[e He]] HP.
    split; first done.
    rewrite HP {HP}.
    iIntros "HaP"; iSplit; last by iIntros "$".
    iIntros "[$|Ha]".
    iApply "HaP".
    iRewrite "Ha".
    by iExists _.
  Qed.

  Global Instance merge_unital_id_free (a : A) :
    IdFree a →
    IsIncludedMergeUnital M a a False True | 5. 
    (* this instance should have higher priority than custom IncludedMergeUnital instances *)
  Proof.
    split; last eauto 10.
    rewrite /IsIncludedMerge; iIntros "#H✓". iSplit; last eauto.
    iDestruct 1 as "[%e #He]". iIntros "!>". (* now drop down to the model *)
    iStopProof. rewrite bi.intuitionistically_elim.
    split => n x Hx. uPred.unseal. repeat (rewrite /uPred_holds /=).
    move => [Hn Ha].  eapply id_freeN_r => //.
  Qed.

  Global Instance merge_unital_last_resort a1 a2 P1 P2:
    IsIncludedMerge M a1 a2 P1 →
    MakeOr P1 (a1 ≡ a2)%I P2 →
    IsIncludedMergeUnital M a1 a2 P1 P2 | 999.
  Proof.
    rewrite /MakeOr => HP1 <-.
    split; first done. 
    iIntros "_"; iSplit; iIntros "[#$|#$]".
  Qed.
End cmra_instances.


Section ucmra_instances.
  Context {A M : ucmra} (a : A).

  Global Instance valid_op_unit_left :
    IsValidOp M a ε a True | 5.
  Proof. apply from_isop. rewrite /IsOp left_id //. Qed.

  Global Instance valid_op_unit_right :
    IsValidOp M a a ε True%I | 5.
  Proof. apply is_valid_op_comm, _. Qed.

  Global Instance has_right_id :
    HasRightId a.
  Proof. exists ε. rewrite right_id //. Qed.
End ucmra_instances.


From iris.algebra Require Import numbers frac dfrac.

Section numbers.
  Context {M : ucmra}.

  Global Instance nat_valid_op (a a1 a2 : nat) : 
    IsOp a a1 a2 → IsValidOp M a a1 a2 True | 10.
  Proof. apply from_isop. Qed.
  Global Instance nat_included_merge (a1 a2 : nat) : IsIncludedMerge M a1 a2 ⌜a1 ≤ a2⌝.
  Proof.
    rewrite /IsIncludedMerge.
    iIntros "_"; iSplit. 
    - by iDestruct 1 as %?%nat_included.
    - iIntros "%". iExists (a2 - a1). iPureIntro. fold_leibniz. rewrite nat_op. lia.
  Qed.

  Global Instance nat_max_valid_op (a a1 a2 : max_nat) :
    IsOp a a1 a2 → IsValidOp M a a1 a2 True | 10.
  Proof. apply from_isop. Qed.
  Global Instance nat_max_included_merge (a1 a2 : nat) : IsIncludedMerge M (MaxNat a1) (MaxNat a2) ⌜a1 ≤ a2⌝.
  Proof.
    rewrite /IsIncludedMerge. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%max_nat_included.
    - iIntros "%". iExists (MaxNat a2). rewrite max_nat_op. iPureIntro. fold_leibniz. f_equal. lia.
  Qed.

  Global Instance nat_min_valid_op (a a1 a2 : min_nat) :
    IsOp a a1 a2 → IsValidOp M a a1 a2 True.
  Proof. apply from_isop. Qed.
  Global Instance nat_min_included_merge (a1 a2 : nat) : IsIncludedMerge M (MinNat a1) (MinNat a2) ⌜a2 ≤ a1⌝.
  Proof.
    rewrite /IsIncludedMerge. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%min_nat_included.
    - iIntros "%". iExists (MinNat a2). rewrite min_nat_op_min. iPureIntro. fold_leibniz. f_equal. lia.
  Qed.
  Global Instance nat_min_has_right_id (a : nat) : HasRightId (MinNat a).
  Proof. exists (MinNat a). rewrite min_nat_op_min. fold_leibniz. f_equal. lia. Qed.

  Global Instance positive_valid_op (a a1 a2 : positive) :
    IsOp a a1 a2 → IsValidOp M a a1 a2 True.
  Proof. apply from_isop. Qed.
  Global Instance positive_included_merge (a1 a2 : positive) : IsIncludedMerge M a1 a2 ⌜(a1 < a2)%positive⌝.
  Proof. 
    rewrite /IsIncludedMerge. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%pos_included.
    - iIntros "%". iExists (a2 - a1)%positive. iPureIntro. fold_leibniz. rewrite pos_op_plus. lia.
  Qed.
  Global Instance positive_included_merge_unital (a1 a2 : positive) : 
    IsIncludedMergeUnital M a1 a2 ⌜(a1 < a2)%positive⌝ ⌜(a1 ≤ a2)%positive⌝ | 20.
  Proof.
    apply: Build_IsIncludedMergeUnital.
    iIntros "_"; iSplit.
    - iIntros "[%|->]"; eauto with lia.
    - iIntros "%H".
      apply Positive_as_DT.le_lteq in H as [Hl| ->]; eauto. 
  Qed.

  Global Instance frac_valid_op (q q1 q2 : Qp) :
    IsOp q q1 q2 → IsValidOp M q q1 q2 ⌜q1 + q2 ≤ 1⌝%Qp%I.
  Proof.
    rewrite /IsOp; split; last by rewrite H; eauto.
    by iDestruct 1 as %?%frac_valid.
  Qed.
  Global Instance frac_included_merge (q1 q2 : Qp) : IsIncludedMerge M q1 q2 ⌜(q1 < q2)%Qp⌝.
  Proof. 
    rewrite /IsIncludedMerge. iIntros "_" ; iSplit.
    - by iDestruct 1 as %?%frac_included.
    - iIntros "%". apply Qp_lt_sum in H as [q' ->]. eauto.
  Qed.
  Global Instance frac_included_merge_unital (q1 q2 : Qp) : IsIncludedMergeUnital M q1 q2 ⌜(q1 < q2)%Qp⌝ ⌜(q1 ≤ q2)%Qp⌝ | 20.
  Proof.
    apply: Build_IsIncludedMergeUnital.
    iIntros "_"; iSplit.
    - iIntros "[%|->]"; eauto. iPureIntro. by apply Qp_lt_le_incl.
    - iIntros "%H".
      destruct (Qp_le_lteq q1 q2) as [[?|?] _]; eauto.
  Qed.

  Global Instance dfrac_valid_op_carry (q q1 q2 : Qp) Pq :
    IsValidOp M q q1 q2 Pq → IsValidOp M (DfracOwn q) (DfracOwn q1) (DfracOwn q2) Pq.
  Proof.
    split.
    - rewrite /op /cmra_op /=. rewrite dfrac_validI -frac_validI.
      destruct H as [H _] => //.
    - destruct H as [_ H].
      rewrite /op /cmra_op /= dfrac_validI -frac_validI H.
      iIntros "->" => //.
  Qed.

  Global Instance dfrac_valid_op_with_discarded_r (q : Qp) :
    IsValidOp M (DfracOwn q ⋅ DfracDiscarded) (DfracOwn q) DfracDiscarded ⌜(q < 1)%Qp⌝.
  Proof. split; [rewrite dfrac_validI | ]; eauto. Qed.

  Global Instance dfrac_valid_op_with_discarded_l (q : Qp) :
    IsValidOp M (DfracOwn q ⋅ DfracDiscarded) DfracDiscarded (DfracOwn q) ⌜(q < 1)%Qp⌝.
  Proof. apply is_valid_op_comm, _. Qed.

  Global Instance dfrac_valid_op_both_discarded (q : Qp) :
    IsValidOp M DfracDiscarded DfracDiscarded DfracDiscarded True.
  Proof. split; eauto. Qed.

  Global Instance dfrac_own_included_merge (q1 q2 : Qp) Pq : 
    IsIncludedMerge M q1 q2 Pq → 
    IsIncludedMerge M (DfracOwn q1) (DfracOwn q2) Pq.
  Proof. 
    rewrite /IsIncludedMerge dfrac_validI -frac_validI => ->.
    iApply bi.wand_iff_trans. iSplit.
    - iDestruct 1 as %?%dfrac_own_included. iPureIntro. by apply frac_included.
    - iDestruct 1 as %[q' ->]%frac_included%Qp_lt_sum.
      by iExists (DfracOwn q').
  Qed.
  Global Instance dfrac_own_included_merge_unital (q1 q2 : Qp) Pq Pq' : 
    IsIncludedMergeUnital M q1 q2 Pq Pq' → 
    IsIncludedMergeUnital M (DfracOwn q1) (DfracOwn q2) Pq Pq' | 20.
  Proof.
    case => Hpq Hpq'. split; first apply _.
    rewrite dfrac_validI -frac_validI Hpq'.
    iApply bi.wand_iff_trans. iSplit.
    - iIntros "[Hpq|%]"; eauto. iRight. case: H => -> //.
    - iIntros "[Hpq|->]"; eauto.
  Qed.
  Global Instance dfrac_own_disc_included_merge (q : Qp) :
    IsIncludedMerge M (DfracOwn q) DfracDiscarded False.
  Proof.
    rewrite /IsIncludedMerge.
    iIntros "_". iSplit => //.
    iIntros "[%dq %Hdq]". destruct dq => //=.
  Qed.
  Global Instance dfrac_disc_own_included_merge (q : Qp) :
    IsIncludedMerge M DfracDiscarded (DfracOwn q) False.
  Proof.
    rewrite /IsIncludedMerge.
    iIntros "_". iSplit => //.
    iIntros "[%dq %Hdq]". destruct dq => //=.
  Qed.
  Global Instance dfrac_disc_disc_included_merge :
    IsIncludedMerge M DfracDiscarded DfracDiscarded True.
  Proof.
    rewrite /IsIncludedMerge.
    iIntros "_". iSplit => //.
    iIntros "_". by iExists DfracDiscarded.
  Qed.
  Global Instance dfrac_discarded_right_id : HasRightId DfracDiscarded.
  Proof. exists DfracDiscarded => //. Qed.
End numbers.


From iris.algebra Require Import gset.

Section sets.
  Context `{Countable K} {M : ucmra}.
  Implicit Types X Y Z : gset K.

  Global Instance set_is_valid_op X Y Z :
    IsOp X Y Z → IsValidOp M X Y Z True | 10.
  Proof. apply from_isop. Qed.
  Global Instance set_included_merge (a1 a2 : gset K) : IsIncludedMerge M a1 a2 ⌜a1 ⊆ a2⌝.
  Proof. 
    rewrite /IsIncludedMerge. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%gset_included. 
    - iIntros "%". iExists a2. iPureIntro. set_solver.
  Qed.

  Global Instance set_disj_is_valid_op X Y :
    IsValidOp M (GSet (X ∪ Y)) (GSet X) (GSet Y) ⌜X ## Y⌝ | 20.
  Proof.
    split.
    - by iDestruct 1 as %?%gset_disj_valid_op.
    - iDestruct 1 as %?%gset_disj_valid_op.
      by rewrite gset_disj_union.
  Qed.
  Global Instance set_disj_valid_op_emp_l X Y :
    IsValidOp M (GSet X) (GSet X) (GSet ∅) True | 10.
  Proof. eapply is_valid_op_weaken; [iSolveTC | eauto ]. Qed.
  Global Instance set_disj_valid_op_emp_r X Y :
    IsValidOp M (GSet X) (GSet ∅) (GSet X) True | 10.
  Proof. apply is_valid_op_comm, _. Qed.
  Global Instance disj_set_included_merge (a1 a2 : gset K) : IsIncludedMerge M (GSet a1) (GSet a2) ⌜a1 ⊆ a2⌝.
  Proof. 
    rewrite /IsIncludedMerge. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%gset_disj_included. 
    - iIntros "%".
      iExists (GSet (a2 ∖ a1)).
      iPureIntro. rewrite gset_disj_union; [|set_solver]. 
      f_equiv. by apply union_difference_L.
  Qed.
End sets.


From iris.algebra Require Import gmultiset.

Section multisets.
  Context `{Countable K} {M : ucmra}.
  Implicit Types X Y Z : gmultiset K.

  Global Instance multiset_is_valid_op X Y Z :
    IsOp X Y Z → IsValidOp M X Y Z True | 10.
  Proof. apply from_isop. Qed.
  Global Instance multiset_included_merge X Y : IsIncludedMerge M X Y ⌜X ⊆ Y⌝.
  Proof. 
    rewrite /IsIncludedMerge. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%gmultiset_included. 
    - iIntros "%". iExists (Y ∖ X). iPureIntro. fold_leibniz. rewrite gmultiset_op. multiset_solver.
  Qed.
End multisets.


From iris.algebra Require Import coPset.

Section coPsets.
  Context {M : ucmra}.
  Implicit Types X Y Z : coPset.

  Global Instance coPset_is_valid_op X Y Z :
    IsOp X Y Z → IsValidOp M X Y Z True | 10.
  Proof. apply from_isop. Qed.
  Global Instance coPset_included_merge X Y : IsIncludedMerge M X Y ⌜X ⊆ Y⌝.
  Proof. 
    rewrite /IsIncludedMerge. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%coPset_included. 
    - iIntros "%". iExists Y. iPureIntro. set_solver.
  Qed.

  Global Instance coPset_disj_is_valid_op X Y :
    IsValidOp M (CoPset (X ∪ Y)) (CoPset X) (CoPset Y) ⌜X ## Y⌝ | 20.
  Proof.
    split.
    - by iDestruct 1 as %?%coPset_disj_valid_op.
    - iDestruct 1 as %?%coPset_disj_valid_op.
      by rewrite coPset_disj_union.
  Qed.
  Global Instance coPset_disj_valid_op_unit_l X Y :
    IsValidOp M (CoPset X) (CoPset X) (CoPset ∅) True | 10.
  Proof. eapply is_valid_op_weaken; [iSolveTC | eauto]. Qed.
  Global Instance coPset_disj_valid_op_unit_r X Y :
    IsValidOp M (CoPset X) (CoPset ∅) (CoPset X) True | 10.
  Proof. apply is_valid_op_comm, _. Qed.
  Global Instance disj_coPset_included_merge X Y : IsIncludedMerge M (CoPset X) (CoPset Y) ⌜X ⊆ Y⌝.
  Proof. 
    rewrite /IsIncludedMerge. iIntros "_"; iSplit.
    - by iDestruct 1 as %?%coPset_disj_included. 
    - iIntros "%".
      iExists (CoPset (Y ∖ X)).
      iPureIntro. rewrite coPset_disj_union; [|set_solver]. 
      f_equiv. by apply union_difference_L.
  Qed.
End coPsets.


Section optional.
  Context {A : cmra} {M : ucmra}.
  Implicit Types a : A.

  Global Instance option_some_valid_op a a1 a2 P :
    IsValidOp M a a1 a2 P → IsValidOp M (Some a) (Some a1) (Some a2) P.
  Proof.
    case => HP Ha.
    split; rewrite -Some_op option_validI //.
    by rewrite Ha option_equivI.
  Qed.
  Global Instance option_included_merge a1 a2 P1 P2 :
    IsIncludedMergeUnital M a1 a2 P1 P2 →
    IsIncludedMerge M (Some a1) (Some a2) P2 | 100.
  Proof.
    rewrite /IsIncludedMerge option_validI => [[HP1 HP2]].
    iIntros "#Ha2".
    iAssert (_)%I as "HP_le"; first by iApply (HP2 with "Ha2").
    iApply bi.wand_iff_trans; last done.
    rewrite HP1.
    iSplit.
    * iDestruct 1 as ([c|]) "Hc".
      + rewrite -Some_op option_equivI.
        iLeft. iApply "Ha2". by iExists c.
      + rewrite Some_op_opM /= option_equivI.
        iRewrite "Hc". eauto.
    * iIntros "[HP|Hr]".
      + iDestruct ("Ha2" with "HP") as "[%c Hc]". iExists (Some c).
        rewrite -Some_op. by iRewrite "Hc".
      + iRewrite "Hr". by iExists None.
  Qed.
  Global Instance option_none_excl_included_merge (ma : optionUR A) :
    IsIncludedMerge M None ma True.
  Proof.
    rewrite /IsIncludedMerge. iIntros "_". iSplit; first by eauto.
    iIntros "_". iExists ma. by rewrite left_id.
  Qed.
  Global Instance option_some_none_excl_included_merge a :
    IsIncludedMerge M (Some a) None False.
  Proof.
    rewrite /IsIncludedMerge. iIntros "_"; iSplit; last done.
    iDestruct 1 as ([c|]) "Hc"; by rewrite option_equivI.
  Qed.

End optional.

From iris.algebra Require Import csum.

Section csum.
  Context {A B : cmra} {M : ucmra}.
  Implicit Types P : uPred M.
  Implicit Types a : A.
  Implicit Types b : B.

  Global Instance sum_inl_valid_op a a1 a2 P :
    IsValidOp _ a a1 a2 P → 
    IsValidOp _ (Cinl a) (Cinl (B := B) a1) (Cinl (B := B) a2) P.
  Proof.
    case => HP Ha. 
    split; rewrite -Cinl_op csum_validI //.
    rewrite Ha.
    iIntros "Ha".
    by iRewrite "Ha".
  Qed.
  Global Instance sum_inr_valid_op b b1 b2 P :
    IsValidOp _ b b1 b2 P → 
    IsValidOp _ (Cinr b) (Cinr (A := A) b1) (Cinr (A := A) b2) P.
  Proof.
    case => HP Ha. 
    split; rewrite -Cinr_op csum_validI //.
    rewrite Ha.
    iIntros "Ha".
    by iRewrite "Ha".
  Qed.
  Global Instance sum_inl_inr_invalid_op a b :
    IsValidOp M (CsumBot) (Cinl (B := B) a) (Cinr (A := A) b) False.
  Proof. split; rewrite /op /= /cmra_op /= csum_validI; eauto. Qed.
  Global Instance sum_inr_inl_invalid_op a b :
    IsValidOp M (CsumBot) (Cinr (A := B) a) (Cinl (B := A) b) False.
  Proof. split; rewrite /op /= /cmra_op /= csum_validI; eauto. Qed.
  Global Instance sum_inl_included_merge a1 a2 P :
    IsIncludedMerge _ a1 a2 P →
    IsIncludedMerge _ (Cinl (B := B) a1) (Cinl (B := B) a2) P | 100.
  Proof.
    rewrite /IsIncludedMerge => HaP.
    iIntros "#H✓"; iSplit.
    - iDestruct 1 as (c) "#Hc".
      rewrite csum_equivI csum_validI.
      destruct c; [ | done..].
      iApply HaP; first done.
      by iExists _.
    - rewrite csum_validI HaP.
      iIntros "#HP".
      iDestruct ("H✓" with "HP") as (c) "Hc".
      iRewrite "Hc".
      by iExists (Cinl _).
  Qed.
  Global Instance sum_inl_included_merge_unital a1 a2 P1 P2 :
    IsIncludedMergeUnital _ a1 a2 P1 P2 →
    IsIncludedMergeUnital _ (Cinl (B := B) a1) (Cinl (B := B) a2) P1 P2 | 100.
  Proof.
    case => HP_lt HP_le; split; first apply _.
    rewrite csum_validI HP_le.
    iApply bi.wand_iff_trans.
    iSplit; iIntros "[$|H]"; iRight; rewrite csum_equivI //.
  Qed.
  Global Instance sum_inr_included_merge b1 b2 P :
    IsIncludedMerge _ b1 b2 P →
    IsIncludedMerge _ (Cinr (A := A) b1) (Cinr (A := A) b2) P | 100.
  Proof.
    rewrite /IsIncludedMerge => HaP.
    iIntros "#H✓"; iSplit.
    - iDestruct 1 as (c) "#Hc".
      rewrite csum_equivI csum_validI.
      destruct c; [ done| |done ].
      iApply HaP; first done.
      by iExists _.
    - rewrite csum_validI HaP.
      iIntros "#HP".
      iSpecialize ("H✓" with "HP").
      iDestruct "H✓" as (c) "Hc".
      iRewrite "Hc".
      by iExists (Cinr c).
  Qed.
  Global Instance sum_inr_included_merge_unital b1 b2 P1 P2 :
    IsIncludedMergeUnital _ b1 b2 P1 P2 →
    IsIncludedMergeUnital _ (Cinr (A := A) b1) (Cinr (A := A) b2) P1 P2 | 100.
  Proof.
    case => HP_lt HP_le; split; first apply _.
    rewrite csum_validI HP_le.
    iApply bi.wand_iff_trans.
    iSplit; iIntros "[$|H]"; iRight; rewrite csum_equivI //.
  Qed.
  Global Instance sum_inl_inr_included_merge a b :
    IsIncludedMerge M (Cinl a) (Cinr b) False | 100.
  Proof.
    rewrite /IsIncludedMerge; iIntros "_"; iSplit; last done.
    iDestruct 1 as ([c|c|]) "#Hc"; rewrite csum_equivI //.
  Qed.
  Global Instance sum_inr_inl_included_merge a b :
    IsIncludedMerge M (Cinr b) (Cinl a) False | 100.
  Proof.
    rewrite /IsIncludedMerge; iIntros "_"; iSplit; last done.
    iDestruct 1 as ([c|c|]) "#Hc"; rewrite csum_equivI //.
  Qed.
  Global Instance csum_right_id_l a :
    HasRightId a → HasRightId (Cinl (B := B) a).
  Proof. 
    move => [r rH].
    exists (Cinl r).
    rewrite -Cinl_op -rH //.
  Qed.
  Global Instance csum_right_id_r b :
    HasRightId b → HasRightId (Cinr (A := A) b).
  Proof. 
    move => [r rH].
    exists (Cinr r).
    rewrite -Cinr_op -rH //.
  Qed.

End csum.


Section prod.
  Context {X Y : cmra} {M : ucmra}.
  Implicit Types x : X.
  Implicit Types y : Y.
  Implicit Types P : uPred M.

  Global Instance prod_valid_op x x1 x2 y y1 y2 P1 P2 P :
    IsValidOp _ x x1 x2 P1 → 
    IsValidOp _ y y1 y2 P2 → 
    MakeAnd P1 P2 P →
    IsValidOp _ (x, y) (x1, y1) (x2, y2) P.
  Proof.
    rewrite /MakeAnd => Hxs Hys HP. split; rewrite -pair_op prod_validI /=.
    - rewrite !is_valid_merge -HP bi.intuitionistically_and //.
    - rewrite prod_equivI /= !is_valid_op //.
  Qed.

  Lemma prod_includedI x1 x2 y1 y2 :
    (x1, y1) ≼ (x2, y2) ⊣⊢@{uPredI M} (x1 ≼ x2) ∧ (y1 ≼ y2).
  Proof.
    apply (anti_symm _).
    - iDestruct 1 as ([x y]) "Hc".
      rewrite -pair_op prod_equivI /=.
      iDestruct "Hc" as "[Hx Hy]"; iSplit; by iExists _.
    - iDestruct 1 as "[[%x Hx] [%y Hy]]".
      iRewrite "Hx"; iRewrite "Hy".
      by iExists (_, _).
  Qed.

  Global Instance prod_included_merge x1 x2 y1 y2 P1 P2 P :
    IsIncludedMerge _ x1 x2 P1 →
    IsIncludedMerge _ y1 y2 P2 →
    MakeAnd P1 P2 P →
    IsIncludedMerge _ (x1, y1) (x2, y2) P.
  Proof.
    rewrite /IsIncludedMerge /MakeAnd => HP1 HP2 <-.
    rewrite bi.intuitionistically_and prod_validI /=.
    rewrite prod_includedI.
    iIntros "[#Hx✓ #Hy✓]"; iSplit.
    - iDestruct 1 as "[Hz1 Hz2]".
      iSplit.
      * by iApply HP1. 
      * by iApply HP2.
    - iIntros "[#HP1 #HP2]".
      rewrite HP1 HP2.
      iSplit.
      * by iApply "Hx✓".
      * by iApply "Hy✓".
  Qed.

  (* This is the most tricky instance of the bunch. 
     The goal of this instance is to obtain good assertions for, i.e. (Some (q, p) ≼ Some (q', p')) (in the cmra: optionUR (prodR fracR positiveR))
     The naive way of doing things would give (q < q' ∧ p < p') ∨ (q = q' ∧ p = p'). We would like to get q ≤ q' and p ≤ p' directly,
      while still allowing the user to look into the disjunction if required. *)
  Global Instance prod_included_merge_unital x1 x2 y1 y2 P1_lt P1_le P2_lt P2_le P_lt P_le P_le' P_lt_case P_lt_case' P_case :
    IsIncludedMergeUnital M x1 x2 P1_lt P1_le → 
    IsIncludedMergeUnital _ y1 y2 P2_lt P2_le →
    MakeAnd P1_le P2_le P_le' →
    MakeAnd P1_lt P2_lt P_lt →
    TCIf (HasRightId x2) (TCEq P_lt_case' True%I) (TCEq P_lt_case' P1_lt) →
    TCIf (HasRightId y2) (TCEq P_lt_case P_lt_case') (MakeAnd P_lt_case' P2_lt P_lt_case) →
    MakeOr P_lt_case (x1 ≡ x2 ∧ y1 ≡ y2)%I P_case → (* MakeOr will simplify True ∨ P ⊣⊢ True *)
    MakeAnd P_le' P_case P_le →
    IsIncludedMergeUnital _ (x1, y1) (x2, y2) P_lt P_le.
  Proof.
    rewrite /MakeAnd /MakeOr /HasRightId => HP1 HP2 HP1P2 HP1P2' HTC1 HTC2 HPcase HPle.
    split.
    { apply: prod_included_merge.
      * apply HP1.
      * apply HP2.
      * done. }
    rewrite prod_validI /= -HPle {HPle} -HPcase {HPcase} -HP1P2 {HP1P2} -HP1P2' {HP1P2'} prod_equivI /=.
    iIntros "[#H✓x #H✓y]".
    iAssert (✓ y2 ∗ ✓ x2)%I as "[H✓y2 H✓x2]"; first by eauto.
    case: HP1 => + HP1. rewrite {1}HP1.
    case: HP2 => + HP2. rewrite {1}HP2.
    rewrite /IsIncludedMerge => HP1' HP2'.
    iSplit.
    - iIntros "[#[Hc1 Hc2]|#[Hc1 Hc2]] !>"; iSplit; [iSplit | | iSplit | by eauto].
      + iApply bi.intuitionistically_elim. iApply "H✓x". eauto.
      + iApply bi.intuitionistically_elim. iApply "H✓y". eauto.
      + iLeft. case: HTC1; case: HTC2.
        * move => _ -> _ -> //.
        * move => <- _ ->. eauto.
        * move => _ -> -> //.
        * move => <- ->. eauto.
      + iApply bi.intuitionistically_elim. iApply "H✓x". eauto.
      + iApply bi.intuitionistically_elim. iApply "H✓y". eauto.
    - iIntros "#[[HP1_le HP2_le] [Hlt|[Hx Hy]]]"; last by iRight; iSplit.
      case: HTC1; case: HTC2.
      * move => Hy -> Hx ->.
        iDestruct ("H✓x" with "HP1_le") as "#[#$|H]".
        + iLeft.
          iDestruct ("H✓y" with "HP2_le") as "#[#$|Hy]".
          iApply (HP1' with "H✓y2"). by iRewrite "Hy".
        + iFrame "H". iDestruct ("H✓y" with "HP2_le") as "#[#$|$]".
          iLeft. iApply (HP2' with "H✓x2"). by iRewrite "H".
      * move => <- Hx ->. rewrite left_id.
        iFrame "Hlt".
        iDestruct ("H✓x" with "HP1_le") as "[#$|H]".
        iLeft.
        iApply (HP2' with "H✓x2"). by iRewrite "H".
      * move => Hy -> ->.
        iFrame "Hlt".
        iDestruct ("H✓y" with "HP2_le") as "[#$|H]".
        iLeft.
        iApply (HP1' with "H✓y2"). by iRewrite "H".
      * move => <- ->. by iLeft.
  Qed.
  Global Instance prod_right_id_both x y :
    HasRightId x → HasRightId y → HasRightId (x, y).
  Proof.
    rewrite /HasRightId.
    case => c Hx1.
    case => c' Hx2.
    exists (c, c').
    by rewrite -pair_op -Hx1 -Hx2.
  Qed.

End prod. 
(* extra instance because TC resolution gets confused for ucmras :( *)
Global Instance prod_included_merge_ucmra {X Y : ucmra} (x1 x2 : X) (y1 y2 : Y) {M} P1 P2 P :
  IsIncludedMerge M x1 x2 P1 →
  IsIncludedMerge M y1 y2 P2 →
  MakeAnd P1 P2 P →
  IsIncludedMerge _ (x1, y1) (x2, y2) P.
Proof. simple eapply prod_included_merge. Qed.

From iris.algebra Require Import excl.

Section excl.
  Context {O : ofe} {M : ucmra}.
  Implicit Types o : O.
  Implicit Types e : excl O.

  Global Instance excl_valid_op e1 e2 :
    IsValidOp M ExclBot e1 e2 False.
  Proof. split; rewrite excl_validI /=; eauto. Qed.
  Global Instance excl_included_merge e1 e2 :
    IsIncludedMerge M e1 e2 False.
  Proof.
    rewrite /IsIncludedMerge. rewrite excl_validI. destruct e2 as [o2|]; last eauto.
    iIntros "_". iSplit; last eauto. iDestruct 1 as (c) "Hc".
    rewrite /op /cmra_op /= /excl_op_instance excl_equivI //.
  Qed.
  Global Instance excl_included_merge_unital o1 o2 :
    IsIncludedMergeUnital M (Excl o1) (Excl o2) False (o1 ≡ o2).
  Proof.
    apply: Build_IsIncludedMergeUnital.
    iIntros "_"; iSplit.
    - iIntros "[[]|#H] !>". rewrite excl_equivI //.
    - iIntros "#H". iRewrite "H". eauto.
  Qed.

End excl.

From iris.algebra Require Import agree.

Section agree.
  Context {O : ofe} {M : ucmra}.
  Implicit Types o : O.

  Global Instance agree_valid_op o1 o2 :
    IsValidOp M (to_agree o1) (to_agree o1) (to_agree o2) (o1 ≡ o2)%I.
  Proof.
    split; rewrite agree_validI agree_equivI; first eauto.
    iIntros "H".
    iRewrite "H".
    by rewrite agree_idemp.
  Qed.
  Global Instance agree_has_right_id o : HasRightId (to_agree o).
  Proof. exists (to_agree o). by rewrite agree_idemp. Qed.
  Lemma to_agree_op_simple (a1 a2 : agree O) o : a1 ⋅ a2 ≡ to_agree o ⊢@{uPredI M} a1 ≡ a2 ∧ a2 ≡ to_agree o.
  Proof.
    iIntros "#Heq".
    iAssert (a1 ≡ a2)%I as "#H".
    - iApply agree_validI.
      by iRewrite "Heq".
    - iFrame "H". iRewrite -"Heq". iRewrite "H". rewrite agree_idemp //.
  Qed.
  Global Instance agree_included_merge_direct o1 o2 :
    IsIncludedMerge M (to_agree o1) (to_agree o2) (o1 ≡ o2) | 10.
  Proof.
    rewrite /IsIncludedMerge.
    iIntros "_". iSplit. 
    - iDestruct 1 as (c) "H2". iDestruct (internal_eq_sym with "H2") as "H".
      rewrite to_agree_op_simple. iDestruct "H" as "[Heq1 Heq2]".
      iRevert "Heq1". iRewrite "Heq2".
      rewrite agree_equivI. eauto.
    - iIntros "#H". iRewrite "H". 
      iExists (to_agree o2). by rewrite agree_idemp.
  Qed.
  Global Instance agree_included_merge_abstract o1 (a : agree O) :
    IsIncludedMerge M (to_agree o1) a (a ≡ to_agree o1) | 20.
  Proof.
    rewrite /IsIncludedMerge.
    iIntros "H✓". iSplit. 
    - iDestruct 1 as (c) "#H2".
      iRevert "H✓".
      iRewrite "H2". iIntros "#Hoc".
      rewrite agree_validI.
      iRewrite -"Hoc". by rewrite agree_idemp.
    - iIntros "#H". iRewrite "H".
      iExists (to_agree o1). by rewrite agree_idemp.
  Qed.

End agree.

From iris.algebra Require Import gmap.

Section gmap.
  Context `{Countable K} {A : cmra} {M : ucmra}.
  Implicit Types m : gmap K A.
  Implicit Types k : K.
  Implicit Types a : A.

  (* move these to algebra/gmap? *)
  Global Instance gmap_is_op m m1 m2 :
    IsOp (merge op m1 m2) m1 m2 | 20.
  Proof. rewrite /IsOp //. Qed.
  Global Instance gmap_is_op_unit_l m :
    IsOp m m ∅ | 10.
  Proof. rewrite /IsOp right_id //. Qed.
  Global Instance gmap_is_op_unit_r m :
    IsOp m ∅ m | 10.
  Proof. rewrite /IsOp left_id //. Qed.

  Global Instance gmap_is_valid_op m m1 m2 :
    IsOp m m1 m2 → IsValidOp M m m1 m2 True | 10.
  Proof. apply from_isop. Qed.
  Global Instance gmap_included_merge m1 m2 : 
    IsIncludedMerge M m1 m2 (∃ m, ∀ i, m2 !! i ≡ m1 !! i ⋅ m !! i) | 100.
  Proof. 
    rewrite /IsIncludedMerge. iIntros "_"; iSplit.
    - iIntros "[%m #Hm] !>". iExists (m).
      iIntros (i). rewrite gmap_equivI -lookup_op. iApply "Hm".
    - iIntros "[%m #Hm]". iExists (m). rewrite gmap_equivI. iIntros (i). rewrite lookup_op. iApply "Hm".
  Qed.
  Global Instance gmap_included_merge_singleton m k a : 
    IsIncludedMerge M {[ k := a ]} m (∃ a', m !! k ≡ Some a' ∧ Some a ≼ Some a' )%I | 50. (* if m !! k would reduce, we could do better *)
  Proof.
    eapply included_merge_weaken; [iSolveTC | ].
    iIntros "#H✓"; iSplit.
    - iIntros "[%m' #Hm] !>".
      iSpecialize ("Hm" $! k). rewrite lookup_singleton //.
      rewrite Some_op_opM.
      iExists (a ⋅? _). iFrame "Hm".
      iExists (m' !! k). rewrite Some_op_opM //.
    - iIntros "#[%a' [Hk [%ma Hma]]] !>". rewrite Some_op_opM (option_equivI (Some a')).
      destruct ma as [a''| ] => /=.
      * iExists (<[k := a'']> m). iIntros (i).
        destruct (decide (k = i)) as [-> | Hneq].
        + rewrite lookup_singleton lookup_insert. iRewrite "Hk". by iApply option_equivI.
        + rewrite lookup_singleton_ne // left_id lookup_insert_ne //.
      * iExists (delete k m). iIntros (i).
        destruct (decide (k = i)) as [-> | Hneq].
        + rewrite lookup_singleton lookup_delete // right_id. by iRewrite -"Hma".
        + rewrite lookup_singleton_ne // left_id lookup_delete_ne //.
  Qed.

End gmap.
(*
From iris.algebra Require Import max_prefix_list.

Section prefix_list.
  Context {O : ofe}.
  Implicit Types l : list O.

  Lemma prefix_or_alt l1 l2 : 
    (∃ l3, l1 ++ l3 ≡ l2) ∨ (∃ l3, l2 ++ l3 ≡ l1) ↔ (take (length l2) l1 ≡ take (length l1) l2).
  Proof.
    wlog: l1 l2 /(length l1 ≤ length l2).
    - intros.
      destruct (decide (length l1 ≤ length l2)) as [Hls|Hls]; first eauto.
      assert (length l2 ≤ length l1) by lia.
      specialize (x _ _ H).
      split.
      * move => [[l3 Hl]|Hl].
        { revert Hls H. rewrite -{1 2}Hl. rewrite app_length. lia. }
        apply symmetry, x. eauto.
      * move => Hl. apply symmetry in Hl. apply x in Hl as [Hl|Hl]; eauto.
    - move => Hl; split => [[Hl1| Hl1]|Hl1].
      * destruct Hl1 as [l3 Hl3]. rewrite -Hl3. rewrite take_app app_length.
        rewrite firstn_all2 //. lia.
      * destruct Hl1 as [l3 Hl3]. revert Hl. rewrite -Hl3. rewrite app_length => Hl. assert (length l3 = 0) by lia.
        assert (l3 = []) as -> by by destruct l3.
        rewrite !right_id //=.
      * left. exists (drop (length l1) l2). rewrite -{2}(take_drop (length l1) l2). f_equiv. rewrite -Hl1. by rewrite firstn_all2.
  Qed.

  Lemma prefix_or_altN n l1 l2 : 
    (∃ l3, l1 ++ l3 ≡{n}≡ l2) ∨ (∃ l3, l2 ++ l3 ≡{n}≡ l1) ↔ (take (length l2) l1 ≡{n}≡ take (length l1) l2).
  Proof.
    wlog: l1 l2 /(length l1 ≤ length l2).
    - intros.
      destruct (decide (length l1 ≤ length l2)) as [Hls|Hls]; first eauto.
      assert (length l2 ≤ length l1) by lia.
      specialize (x _ _ H).
      split.
      * move => [[l3 Hl]|Hl].
        { revert Hls H. rewrite -{1 2}Hl. rewrite app_length. lia. }
        apply symmetry, x. eauto.
      * move => Hl. apply symmetry in Hl. apply x in Hl as [Hl|Hl]; eauto.
    - move => Hl; split => [[Hl1| Hl1]|Hl1].
      * destruct Hl1 as [l3 Hl3]. rewrite -Hl3. rewrite take_app app_length.
        rewrite firstn_all2 //. lia.
      * destruct Hl1 as [l3 Hl3]. revert Hl. rewrite -Hl3. rewrite app_length => Hl. assert (length l3 = 0) by lia.
        assert (l3 = []) as -> by by destruct l3.
        rewrite !right_id //=.
      * left. exists (drop (length l1) l2). rewrite -{2}(take_drop (length l1) l2). f_equiv. rewrite -Hl1. by rewrite firstn_all2.
  Qed.

  Definition longest_of l1 l2 := take (length l2) l1 ++ drop (length l1) l2 ++ drop (length l2) l1.

  Global Instance longest_of_ne : NonExpansive2 longest_of.
  Proof.
    rewrite /longest_of => n l1 l1' Hl1 l2 l2' Hl2 /=. rewrite Hl1. clear l1 Hl1.
    assert (length l2 = length l2') as ->. rewrite Hl2 //.
    by repeat f_equiv.
  Qed.

  Lemma prefix_to_max_1 l1 l2 : 
    (∃ l3, l1 ++ l3 ≡ l2) → longest_of l1 l2 ≡ l2.
  Proof.
    move => [l3 Hl3]. rewrite /longest_of.
    (* we would like to do 'rewrite -Hl3.' but finding the Proper instances takes forever *)
    assert (take (length l2) l1 ≡ l1) as ->.
    { rewrite -Hl3 app_length firstn_all2 //. lia. }
    assert (drop (length l2) l1 ≡ []) as ->.
    { rewrite -Hl3 app_length skipn_all2 //. lia. }
    rewrite right_id -Hl3.
    rewrite drop_app //.
  Qed.

  Lemma prefix_to_max_2 l1 l2 : 
    (∃ l3, l1 ++ l3 ≡ l2) → longest_of l2 l1 ≡ l2.
  Proof.
    move => [l3 Hl3]. rewrite /longest_of.
    assert (drop (length l2) l1 ≡ []) as -> => /=.
    { rewrite -Hl3 app_length skipn_all2 //. lia. }
    rewrite take_drop //.
  Qed.

  Lemma longest_of_comm_if_one_prefix l1 l2 : 
    (take (length l2) l1 ≡ take (length l1) l2) → longest_of l1 l2 ≡ longest_of l2 l1.
  Proof.
    move => /prefix_or_alt [Hl3|Hl3].
    - rewrite prefix_to_max_1 // prefix_to_max_2 //.
    - rewrite prefix_to_max_2 // prefix_to_max_1 //.
  Qed.

  Lemma longest_of_idemp l : longest_of l l = l.
  Proof. rewrite /longest_of firstn_all skipn_all !right_id //. Qed.

  Context {M : ucmra}.

  Lemma longest_of_comm_if_one_prefix_int l1 l2 : 
    (take (length l2) l1 ≡ take (length l1) l2) ⊢@{uPredI M} longest_of l1 l2 ≡ longest_of l2 l1.
  Proof.
    iIntros "#Hl".
    rewrite /longest_of.
    iRewrite "Hl".
    iAssert (drop (length l1) l2 ++ drop (length l2) l1 ≡ drop (length l2) l1 ++ drop (length l1) l2)%I as "Heq"; last first.
    { by iRewrite "Heq". }
    destruct (decide (length l1 ≤ length l2)) as [Hls|Hls].
    - rewrite (skipn_all2 l1) //= right_id //.
    - assert (length l2 ≤ length l1) by lia.
      rewrite skipn_all2 //= right_id //.
  Qed.

  Lemma prefix_or_altI l1 l2 : 
    (∃ l3, l1 ++ l3 ≡ l2) ∨ (∃ l3, l2 ++ l3 ≡ l1) ⊣⊢@{uPredI M} (take (length l2) l1 ≡ take (length l1) l2).
  Proof.
    wlog: l1 l2 /(length l1 ≤ length l2).
    - intros.
      destruct (decide (length l1 ≤ length l2)) as [Hls|Hls]; first eauto.
      assert (length l2 ≤ length l1) by lia.
      specialize (x _ _ H); iSplit.
      * iIntros "[[%l3 Hl]|Hl]".
        { iAssert ⌜length (l1 ++ l3) = length l2⌝%I as %?; first by by iRewrite "Hl". rewrite app_length in H0. lia. }
        iApply internal_eq_sym. iApply x. eauto.
      * iIntros "Hl". 
        iDestruct (internal_eq_sym with "Hl") as "Hl".
        iDestruct (x with "Hl") as "[Hl|Hl]"; eauto.
    - move => Hl; iSplit. iIntros "[[%l3 Hl3]|[%l3 Hl3]]".
      * iRewrite -"Hl3". rewrite take_app app_length.
        rewrite firstn_all2 //. lia.
      * iRewrite -"Hl3". rewrite app_length take_app firstn_all2 //. lia.
      * iIntros "Hl". iLeft. iExists (drop (length l1) l2). rewrite -{4}(take_drop (length l1) l2). iRewrite -"Hl". by rewrite firstn_all2.
  Qed.

  Lemma max_prefix_op_validI l1 l2 :
    ✓ (to_max_prefix_list l1 ⋅ to_max_prefix_list l2) ⊢@{uPredI M} take (length l2) l1 ≡ take (length l1) l2.
  Proof.
    uPred.unseal. split => n x Hx.
    rewrite /uPred_cmra_valid_def /= /uPred_holds /=.
    move => /to_max_prefix_list_op_validN => [[[l Hls]|[l Hls]]]; eapply prefix_or_altN; naive_solver.
  Qed.

  Lemma max_prefix_op_idemp l : to_max_prefix_list l ⋅ to_max_prefix_list l ≡ to_max_prefix_list l.
  Proof. 
    apply equiv_dist => n i.
    rewrite lookup_op.
    change (ofe_car $ agreeO O) with (cmra_car $ agreeR O). (* fun fun fun *)
    match goal with | |- ?c ⋅ ?c ≡{n}≡ ?c => generalize c end.
    case; last done. move => a.
    rewrite -Some_op agree_idemp //.
  Qed.

  Global Instance is_valid_op_prefix l1 l2 :
    IsValidOp (to_max_prefix_list $ longest_of l1 l2) (to_max_prefix_list l1) (to_max_prefix_list l2) M (take (length l2) l1 ≡ take (length l1) l2).
  Proof.
    wlog: l1 l2 /(length l1 ≤ length l2).
    - intros.
      destruct (decide (length l1 ≤ length l2)) as [Hls|Hls]; first eauto.
      assert (length l2 ≤ length l1) by lia.
      apply is_valid_op_comm.
      specialize (x _ _ H) as [Hv Heq].
      split.
      * rewrite Hv. iIntros "#Heq". by iRewrite "Heq".
      * iIntros "#H✓".
        iAssert (take (length l1) l2 ≡ take (length l2) l1)%I as "Htake".
        { iApply bi.intuitionistically_elim. by iApply Hv. }
        rewrite Heq. iRewrite -"H✓".
        iDestruct (longest_of_comm_if_one_prefix_int with "Htake") as "Heq".
        by iRewrite "Heq".
    - intros. split; rewrite max_prefix_op_validI; first by eauto.
      iIntros "#Hpf".
      iDestruct (longest_of_comm_if_one_prefix_int with "Hpf") as "Heq".
      rewrite -prefix_or_altI.
      iDestruct "Hpf" as "[[%l3 Hl3]|[%l3 Hl3]]".
      * iRewrite "Heq". iClear "Heq".
        iAssert (to_max_prefix_list l2 ≡ to_max_prefix_list (l1 ++ l3))%I as "Heq2"; first by iRewrite -"Hl3".
        iRewrite "Heq2". iClear "Heq2".
        rewrite max_prefix_list.to_max_prefix_list_app.
        rewrite assoc. rewrite max_prefix_op_idemp.
        rewrite -max_prefix_list.to_max_prefix_list_app.
        rewrite /longest_of.
        rewrite skipn_all2 //= take_drop. by iRewrite -"Hl3".
      * destruct l3; last first.
        { iAssert ⌜length l2 < length l1⌝%I as %?. iRewrite -"Hl3". rewrite app_length /=. eauto with lia. lia. }
        rewrite right_id.
        iRewrite "Hl3". iClear "Hl3".
        rewrite longest_of_idemp max_prefix_op_idemp //.
  Qed.

End prefix_list. *)

From iris.algebra Require Import reservation_map.

Section reservation_map.
  Context {A : cmra} {M : ucmra}.
  Implicit Types a b : A.
  Implicit Types x y : reservation_map A.
  Implicit Types k : positive.
  Implicit Types P : uPred M.

  Lemma reservation_op_validI x y :
    ✓ (x ⋅ y) ⊢@{uPredI M} ✓ (reservation_map_data_proj x ⋅ reservation_map_data_proj y) ∧ ✓ (reservation_map_token_proj x ⋅ reservation_map_token_proj y).
  Proof.
    destruct x as [xm xE].
    destruct y as [ym yE].
    split => n. uPred.unseal => // a Ha /=.
    rewrite /uPred_holds /= reservation_map_validN_eq.
    rewrite {1}/op /cmra_op /=.
    destruct xE as [E1|]; destruct yE as [E2|] => //=.
    rewrite {1}/op /cmra_op /=.
    destruct (decide (E1 ## E2)) => //.
    move => [H1 H2].
    split => //.
    rewrite /uPred_holds /=.
    rewrite /op /cmra_op /=.
    rewrite decide_True //.
  Qed.

  Lemma reservation_equivI x y :
    x ≡ y ⊣⊢@{uPredI M} (reservation_map_data_proj x ≡ reservation_map_data_proj y) ∧ (reservation_map_token_proj x ≡ reservation_map_token_proj y).
  Proof. split => n. uPred.unseal => //. Qed.

  Lemma reservation_token_valid_combineI E1 E2 : 
    ✓ (reservation_map_token (A := A) E1 ⋅ reservation_map_token E2) ⊢@{uPredI M} ⌜E1 ## E2⌝.
  Proof. rewrite reservation_op_validI /= bi.and_elim_r is_valid_merge; eauto. Qed.

  Global Instance combine_reservation_token E1 E2 :
    IsValidOp M (reservation_map_token (A := A) (E1 ∪ E2)) (reservation_map_token E1) (reservation_map_token E2) ⌜E1 ## E2⌝.
  Proof.
    split.
    - rewrite reservation_token_valid_combineI; eauto.
    - rewrite reservation_token_valid_combineI. iIntros "%".
      rewrite reservation_map_token_union //.
  Qed.

  Lemma reservation_map_data_validI k b :
    ✓ reservation_map_data k b ⊣⊢@{uPredI M} ✓ b.
  Proof.
    split => n. uPred.unseal => //.
    rewrite /uPred_holds /= reservation_map_validN_eq /=.
    move => x Hx.
    rewrite singleton_validN.
    split; naive_solver.
  Qed.

  Global Instance combine_reservation_data k b b1 b2 P :
    IsValidOp _ b b1 b2 P →
    IsValidOp _ (reservation_map_data k b) (reservation_map_data k b1) (reservation_map_data k b2) P.
  Proof.
    split; rewrite -reservation_map_data_op reservation_map_data_validI.
    - apply H. 
    - rewrite is_valid_op.
      iIntros "Heq".
      by iRewrite "Heq".
  Qed.

  Global Instance reservation_token_included_merge E1 E2 P :
    IsIncludedMerge _ (CoPset E1) (CoPset E2) P →
    IsIncludedMerge _ (reservation_map_token (A := A) E1) (reservation_map_token E2) P.
  Proof.
    rewrite /IsIncludedMerge.
    iIntros (HP) "H✓"; iSplit.
    - iIntros "[%m #Hm]". iRevert "H✓".
      destruct m as [m mE].
      iRewrite "Hm".
      rewrite reservation_op_validI /=.
      rewrite reservation_equivI /=.
      destruct mE as [E|]; last by iIntros "[_ %]".
      rewrite !is_valid_merge.
      iIntros "[_ %]".
      iApply HP; first done.
      iExists (CoPset E).
      iDestruct "Hm" as "[_ $]".
    - iIntros "#HP".
      iAssert (CoPset E1 ≼ CoPset E2)%I as "[%E HE]"; first by iApply HP.
      iExists (ReservationMap ∅ E).
      rewrite reservation_equivI /=. iSplit => //. by rewrite right_id.
  Qed.

  Global Instance reservation_data_included_merge k b1 b2 P :
    IsIncludedMerge _ (Some b1) (Some b2) P →
    IsIncludedMerge _ (reservation_map_data k b1) (reservation_map_data k b2) P.
  Proof.
    rewrite /IsIncludedMerge option_validI.
    iIntros (HP) "H✓". rewrite reservation_map_data_validI HP.
    iRevert "H✓". iApply bi.wand_iff_trans. iSplit.
    - iIntros "[%m #Hm]".
      destruct m as [m mE].
      rewrite reservation_equivI /=.
      iDestruct "Hm" as "[Hkm _]".
      rewrite gmap_equivI.
      iSpecialize ("Hkm" $! k).
      rewrite lookup_op !lookup_singleton.
      by iExists (m !! k).
    - iIntros "[%mb Hmb]".
      destruct mb as [b|].
      * rewrite -Some_op option_equivI. iRewrite "Hmb".
        iExists (reservation_map_data k b).
        rewrite reservation_equivI /= !right_id singleton_op //.
      * rewrite right_id option_equivI. iRewrite "Hmb".
        iExists (ReservationMap ε ε). by rewrite right_id.
  Qed.

End reservation_map.

From iris.algebra Require Import view.

Section view.
  Context {A : ofe} {B M : ucmra} {rel : view_rel A B}.
  Implicit Types a : A.
  Implicit Types b : B.
  Implicit Types P : uPred M.
  Implicit Types v : viewR rel.

  Program Definition rel_holds_for a b : uPred M := UPred _ (λ n _, rel n a b) _.
  Next Obligation.
    move => /= a b n1 n2 x1 x2 Hb Hx Hn.
    eapply view_rel_mono => //.
  Qed.
  Global Instance rel_holds_for_persistent a b : Persistent (rel_holds_for a b).
  Proof. rewrite /Persistent. by uPred.unseal. Qed.
  Global Instance rel_holds_proper1 : NonExpansive2 rel_holds_for.
  Proof.
    move => n a a' Ha b b' Hb /=.
    split. rewrite /uPred_holds /= => n' x Hn Hx.
    split => Hr; eapply view_rel_mono => //=.
    - by eapply dist_le.
    - exists ε. rewrite right_id. eauto using dist_le.
    - eapply dist_le; last done. rewrite Ha //.
    - exists ε. rewrite right_id. eapply dist_le; last done. rewrite Hb //.
  Qed.
  Global Instance rel_holds_proper2 : Proper ((≡) ==> (≡) ==> (⊣⊢)) rel_holds_for.
  Proof. 
    move => a a' Ha b b' Hb /=.
    split. rewrite /uPred_holds /= => n' x Hx. rewrite Ha Hb //.
  Qed.

  Lemma view_validI v :
    ✓ v ⊣⊢@{uPredI M} match view_auth_proj v with
          | Some (dq, a) =>
            ∃ a', a ≡ to_agree a' ∧ v ≡ ●V{dq} a' ⋅ ◯V (view_frag_proj v) ∧ rel_holds_for a' (view_frag_proj v) ∧ ✓ dq
          | None => v ≡ ◯V (view_frag_proj v) ∧ ∃ a, rel_holds_for a (view_frag_proj v)
          end.
  Proof.
    destruct v as [[[dq a]|] b] => /=.
    - uPred.unseal.
      split=> n y Hy.
      rewrite /uPred_cmra_valid_def /= /validN /cmra_validN /= /view_validN_instance /=.
      split.
      * case => Hdq [a' [Ha1 Ha2]].
        exists a'.
        split => //=.
        split => //=.
        rewrite /uPred_holds /= Ha1 /op /cmra_op /= /view_op_instance /= right_id left_id //.
      * repeat (rewrite /uPred_holds /=). naive_solver.
    - uPred.unseal. split => n y Hy //=.
      repeat (rewrite /uPred_holds /=). naive_solver.
  Qed.

  Lemma view_equivI v1 v2 :
    v1 ≡ v2 ⊣⊢@{uPredI M} view_auth_proj v1 ≡ view_auth_proj v2 ∧ view_frag_proj v1 ≡ view_frag_proj v2.
  Proof. uPred.unseal; split => n y Hy //. Qed.

  Lemma view_frag_valid_op_gen b b1 b2 :
    ((∃ a, rel_holds_for a (b1 ⋅ b2)) ⊢ b ≡ b1 ⋅ b2) → (* generic views do not require the fragment to be valid! *)
    IsValidOp M (view_frag (rel := rel) b) (◯V b1) (◯V b2) (∃ a, rel_holds_for a b).
  Proof.
    move => Hb.
    split; rewrite -view_frag_op.
    - iIntros "#H !>".
      rewrite view_validI //=.
      iDestruct "H" as "[_ #H]".
      iAssert (b ≡ b1 ⋅ b2)%I as "Hb"; first by iApply Hb.
      iDestruct "H" as "[%a H]".
      iExists a. by iRewrite "Hb".
    - rewrite view_validI /=.
      rewrite Hb.
      iIntros "[_ Heq]". by iRewrite "Heq".
  Qed.

  Global Instance view_frag_valid_op b b1 b2 P :
    IsOp b b1 b2 → (* generic views do not require the fragment to be valid! *)
    IsValidOp M (view_frag (rel := rel) b) (◯V b1) (◯V b2) (∃ a, rel_holds_for a b).
  Proof.
    intros. eapply view_frag_valid_op_gen.
    rewrite /IsOp in H. rewrite H. eauto.
  Qed.

  Lemma view_auth_dfrac_op_validI dq1 dq2 a1 a2 : ✓ (view_auth (rel := rel) dq1 a1 ⋅ ●V{dq2} a2) ⊣⊢@{uPredI M} ✓ (dq1 ⋅ dq2) ∧ (a1 ≡ a2) ∧ rel_holds_for a2 ε.
  Proof.
    apply (anti_symm _); last first.
    - iIntros "(% & Ha & Hrel)".
      iRewrite "Ha".
      rewrite view_validI /=.
      iExists a2.
      rewrite agree_idemp -view_auth_dfrac_op !right_id.
      iSplit; first done.
      iSplit; last eauto.
      rewrite {2}/op /= /cmra_op /= /view_op_instance /= !right_id //.
    - rewrite view_validI /=.
      iDestruct 1 as (a) "Ha". rewrite to_agree_op_simple !agree_equivI /= right_id.
      iDestruct "Ha" as "([$ #Heq] & _ & H & %)".
      iRewrite "Heq". eauto.
  Qed.

  Global Instance view_auth_dfrac_own_valid_op a1 a2 dq dq1 dq2 Pq :
    IsValidOp M dq dq1 dq2 Pq →
    IsValidOp M (view_auth (rel := rel) dq a1) (●V{dq1} a1) (●V{dq2} a2) (Pq ∧ a1 ≡ a2 ∧ rel_holds_for a2 ε)%I.
  Proof.
    intros.
    split.
    - rewrite view_auth_dfrac_op_validI is_valid_merge.
      iIntros "(#$ & #$ & #$)".
    - rewrite view_auth_dfrac_op_validI is_valid_op.
      iIntros "(-> & Heq & _)".
      iRewrite "Heq".
      rewrite -view_auth_dfrac_op //.
  Qed.
  (* it is possible to add IncludedMerge classes for views, but that would probably be painful, and only relevant
     for the case where ●V appears nested under another ●. I think usually better ways should exist? *)  

End view.

Global Arguments rel_holds_for {A B M} rel _ _.

From iris.algebra Require Import auth.

Section auth.
  Context {A M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  Global Instance auth_frag_valid_op a a1 a2 P :
    IsValidOp M a a1 a2 P →
    IsValidOp M (◯ a) (◯ a1) (◯ a2) P.
  Proof.
    move => HPa.
    split; rewrite -auth_frag_op auth_frag_validI //.
    - rewrite is_valid_merge //.
    - rewrite is_valid_op.
      iIntros "H".
      by iRewrite "H".
  Qed.
  Lemma auth_rel_holds a1 a2 : rel_holds_for auth_view_rel a1 a2 ⊣⊢@{uPredI M} a2 ≼ a1 ∧ ✓ a1.
  Proof. split => n. rewrite /includedI. uPred.unseal => //. Qed.
  Lemma auth_auth_dfrac_op_validI dq1 dq2 a1 a2 : ✓ (●{dq1} a1 ⋅ ●{dq2} a2) ⊣⊢@{uPredI M} ✓ (dq1 ⋅ dq2) ∧ ✓ a2 ∧ (a1 ≡ a2).
  Proof.
    rewrite view_auth_dfrac_op_validI auth_rel_holds.
    eapply (anti_symm _); eauto with iFrame.
    - iIntros "($ & $ & _ & $)".
    - iIntros "($ & $ & $)". iExists a2. by rewrite left_id.
  Qed.
  Global Instance auth_auth_dfrac_own_valid_op a1 a2 dq dq1 dq2 Pq :
    IsValidOp M dq dq1 dq2 Pq →
    IsValidOp M (●{dq} a1) (●{dq1} a1) (●{dq2} a2) (Pq ∧ a1 ≡ a2).
  Proof.
    intros.
    split.
    - rewrite auth_auth_dfrac_op_validI is_valid_merge.
      iIntros "(#$ & _ & #$)".
    - rewrite auth_auth_dfrac_op_validI is_valid_op.
      iIntros "(-> & _ & #Ha)".
      iRewrite -"Ha".
      rewrite -auth_auth_dfrac_op //.
  Qed.
End auth.

From iris.algebra Require Import frac_auth.

Section frac_auth.
  Context {A : cmra} {M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  (* overcomes the typeclasses opaque instance on frac_auth_frag *)
  Global Instance frac_auth_frag_valid_op a a1 a2 (q q1 q2 : Qp) P1 P2 :
    IsValidOp M q q1 q2 P1 →
    IsValidOp M a a1 a2 P2 →
    IsValidOp M (◯F{q} a) (◯F{q1} a1) (◯F{q2} a2) (P1 ∧ P2).
  Proof.
    intros.
    apply auth_frag_valid_op, option_some_valid_op.
    by eapply prod_valid_op.
  Qed.
End frac_auth.

From iris.algebra Require Import excl_auth.

Section excl_auth.
  Context {A : ofe} {M : ucmra}.
  Implicit Types a : A.
  Implicit Types P : uPred M.

  (* overcomes the typeclasses opaque instance on excl_auth_frag *)
  Global Instance excl_auth_frag_valid_op ea a1 a2 P :
    IsValidOp M (Some ea) (Excl' a1) (Excl' a2) P →
    IsValidOp M (◯ (Some ea)) (◯E a1) (◯E a2) P.
  Proof. apply auth_frag_valid_op. Qed.
End excl_auth.

From iris.algebra.lib Require Import gmap_view.

Section gmap_view.
  Context {K : Type} `{Countable K} {V : ofe} {M : ucmra}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dq : dfrac) (v : V).
  Implicit Types P : uPred M.

  Lemma gmap_view_rel_holds (m : gmap K V) (f : gmap K (dfrac * agree V)) : 
    rel_holds_for (gmap_view.gmap_view_rel K V) m f ⊣⊢@{uPredI M} ∀ (i : K) dq a, ⌜f !! i = Some (dq, a)⌝ → ∃ a', a ≡ to_agree a' ∧ ✓ dq ∧ ⌜m !! i = Some a'⌝.
  Proof. 
    split => n x Hx. rewrite /includedI. uPred.unseal.
    repeat (rewrite /uPred_holds /=).
    rewrite /gmap_view.gmap_view_rel_raw /=. split.
    - move => /map_Forall_lookup Hm k dq a n' x' Hx' Hn Hx'' /Hm /= => [[v [Hv1 [Hv2 Hv3]]]].
      exists v. rewrite Hv3. split; eauto using dist_le'.
    - intros. apply map_Forall_lookup => k [dq a] /= /H0 {H0} H0'.
      specialize (H0' n x).
      destruct H0' as [v Hv] => //. eauto.
  Qed.

  Lemma gmap_view_rel_holds_singleton k dv m :
    rel_holds_for (gmap_view.gmap_view_rel K V) m {[ k := dv ]} ⊣⊢@{uPredI M} ∃ a', dv.2 ≡ to_agree a' ∧ ✓ dv.1 ∧ ⌜m !! k = Some a'⌝.
  Proof.
    rewrite gmap_view_rel_holds.
    apply (anti_symm _).
    - iIntros "Hm". destruct dv as [dq av] => /=.
      iApply ("Hm" $! k dq av). rewrite lookup_singleton //.
    - iDestruct 1 as "[%a (Ha1 & Ha2 & %)]".
      iIntros (i). destruct (decide (k = i)) as [->|Hneq].
      * rewrite lookup_singleton /= H0 {H0 i}.
        iIntros (dq av Hdq). case: Hdq => -> /=.
        iExists _. eauto. 
      * rewrite lookup_singleton_ne //.
  Qed.

  Global Instance gmap_view_frag_valid_op k dq dq1 dq2 v1 v2 P :
    IsValidOp _ dq dq1 dq2 P →
    IsValidOp _ (gmap_view_frag k dq v1) (gmap_view_frag k dq1 v1) (gmap_view_frag k dq2 v2) (P ∧ v1 ≡ v2).
  Proof.
    intros.
    eapply is_valid_op_weaken; first eapply view_frag_valid_op_gen.
    - iDestruct 1 as (m) "Hm".
      rewrite singleton_op -pair_op gmap_view_rel_holds_singleton /=.
      iDestruct "Hm" as "[%v3 (Hv3 & Hv3' & _)]".
      rewrite to_agree_op_simple is_valid_op.
      iDestruct "Hv3" as "[Heq _]". iRewrite "Heq".
      iRewrite "Hv3'". rewrite agree_idemp //.
    - rewrite view_validI /=.
      iIntros "[[_ [%m Hm]] _]".
      rewrite singleton_op -pair_op.
      rewrite gmap_view_rel_holds_singleton /=.
      iDestruct "Hm" as "[%v3 (#Hv3 & #Hv3' & %)]".
      rewrite to_agree_op_simple bi.and_elim_l agree_equivI. rewrite is_valid_merge.
      rewrite bi.intuitionistically_elim.
      iFrame "#".
  Qed.

  Global Instance gmap_view_auth_valid_op dq dq1 dq2 P m1 m2 :
    IsValidOp _ dq dq1 dq2 P →
    IsValidOp _ (gmap_view_auth dq m1) (gmap_view_auth dq1 m1) (gmap_view_auth dq2 m2) (P ∧ m1 ≡ m2).
  Proof.
    intros. eapply is_valid_op_weaken.
    - rewrite /gmap_view_auth. iSolveTC.
    - iIntros "(_ & #$ & #$ & _ )".
  Qed.

End gmap_view.

(*
Section auth_inclusion.
  Context {M : ucmra}.

  Lemma view_includedI {A B} {rel : view_rel A B} (v1 v2 : viewR rel) :
    v1 ≼ v2 ⊢@{uPredI M} ✓ v2 -∗ view_frag_proj v1 ≼ view_frag_proj v2 ∧ 
      match view_auth_proj v2, view_auth_proj v1 with
      | (Some (dqu, au)), (Some (dql, al)) => (Some dql) ≼ (Some dqu) ∧ al ≼ au (* this only gives al ≡ au if ✓ au, which is usually dependent on rel *)
      | None, (Some (dql, al)) => False
      | _, _ => True
      end.
  Proof.
    iIntros "[%el #H] #Hvu".
    iAssert (✓ el)%I as "Hel".
    { iRevert "Hvu". iRewrite "H". rewrite comm uPred.cmra_valid_weaken. eauto. }
    rewrite (view_uninjI el).
    destruct el as [[[dq3 a3]|] b_frac] => /=.
    - iDestruct "Hel" as "[%a' [#Ha #Hel]]".
      iRevert "H". iRewrite "Hel". iClear "Hel Ha". clear a3.
      destruct v2 as [vua vuf]; destruct v1 as [vla vlf] => /=.
      rewrite view_equivI /=.
      iIntros "[#Hva #Hvf]". rewrite right_id left_id. iSplit; first by iExists b_frac.
      destruct vua as [[vuq vua]|]; destruct vla as [[vlq vla]|] => //.
      * rewrite -Some_op /= -pair_op.
        rewrite option_equivI prod_equivI /=.
        iDestruct "Hva" as "[Hvq Hva]".
        iSplit; last by iExists _.
        iExists (Some dq3). rewrite -Some_op. by iRewrite "Hvq".
      * rewrite -Some_op /= -pair_op.
        by rewrite option_equivI.
    - iClear "Hel".
      rewrite view_equivI /= right_id.
      iDestruct "H" as "[Ha Hf]".
      iSplit; first by iExists b_frac.
      destruct v2 as [vua vuf]; destruct v1 as [vla vlf] => //=.
      destruct vua as [[vuq vua]|]; destruct vla as [[vlq vla]|] => //=; rewrite option_equivI //.
      rewrite prod_equivI /=.
      iDestruct "Ha" as "[Hq Ha]".
      iRewrite "Hq". iSplit; first by iExists None.
      iExists vla.
      rewrite agree_idemp //.
  Qed.

  Global Instance auth_auth_included {A : ucmra} (a1 a2 : A) (dq1 dq2 : dfrac) Pq Pq' :
    IsIncludedMerge (Some dq1) (Some dq2) M Pq →
    MakeAnd Pq (a1 ≡ a2) Pq' →
    IsIncludedMerge (●{dq1} a1) (●{dq2} a2) M Pq'.
  Proof.
    rewrite /IsIncludedMerge /MakeAnd => Hdq <-.
    iIntros "#Ha2".
    iSplit.
    - iIntros "#Hi".
      rewrite view_includedI /=.
      iDestruct ("Hi" with "Ha2") as "(_ & Hdq & Ha1)"; iClear "Hi".
      rewrite auth_auth_dfrac_validI. iDestruct "Ha2" as "[% Ha2]".
      rewrite bi.intuitionistically_and.
      iSplit; first by iApply Hdq => //.
      rewrite is_included_merge'.
      iApply "Ha1" => //.
    - iIntros "[#HPq #Ha]".
      iRewrite "Ha"; iClear "Ha".
      rewrite auth_auth_dfrac_validI. iDestruct "Ha2" as "[% _]".
      iAssert (Some dq1 ≼ Some dq2)%I as "#[%dq Hqs]".
      iApply Hdq => //.
      destruct dq as [q|].
      * iExists (●{q} a2).
        rewrite -auth_auth_dfrac_op -Some_op.
        rewrite option_equivI. by iRewrite "Hqs".
      * rewrite right_id option_equivI.
        iRewrite "Hqs".
        iExists ε. rewrite right_id //.
  Qed.

  Global Instance frag_auth_included {A : ucmra} (a1 a2 : A) (dq2 : dfrac) Pq :
    IsIncludedMerge a1 ε M Pq →
    IsIncludedMerge (◯ a1) (●{dq2} a2) M Pq.
  Proof.
    rewrite /IsIncludedMerge => Hdq.
    iIntros "#Ha2".
    iSplit.
    - iIntros "#Hi".
      rewrite view_includedI /=.
      iDestruct ("Hi" with "Ha2") as "[Hi' _ ]".
      iApply Hdq => //.
      eauto using ucmra_unit_valid.
    - iIntros "#Hpq".
      iAssert (a1 ≼ ε)%I as "[%a' #Ha1]".
      { iApply Hdq => //. eauto using ucmra_unit_valid. }
      iExists (◯ a' ⋅ ●{dq2} a2).
      rewrite assoc -auth_frag_op.
      rewrite view_equivI /= left_id right_id.
      iSplit => //.
  Qed.

  (* i guess in practice we will always have a2 = a3? *)
  Global Instance frag_auth_frag_included {A : ucmra} (a1 a2 a3 : A) (dq2 : dfrac) Pq :
    IsIncludedMerge a1 a3 M Pq →
    IsIncludedMerge (◯ a1) (●{dq2} a2 ⋅ ◯ a3) M Pq.
  Proof.
    rewrite /IsIncludedMerge => Hdq.
    iIntros "#Ha2".
    iSplit.
    - iIntros "#Hi".
      rewrite view_includedI /= left_id right_id.
      iSpecialize ("Hi" with "Ha2").
      iApply Hdq => //.
      rewrite auth_both_dfrac_validI.
      iDestruct "Ha2" as "(_ & [%a' Ha] & Ha2)".
      iApply (uPred.cmra_valid_weaken _ a'). iRevert "Ha2". iRewrite "Ha". eauto.
    - iIntros "#Hpq".
      iAssert (a1 ≼ a3)%I as "[%a' #Ha1]".
      { iApply Hdq => //. rewrite comm uPred.cmra_valid_weaken auth_frag_validI //. }
      iExists (◯ a' ⋅ ●{dq2} a2).
      rewrite assoc -auth_frag_op.
      rewrite view_equivI /= !left_id !right_id.
      iSplit => //.
  Qed.

  Global Instance auth_auth_frag_included {A : ucmra} (a1 a2 a3 : A) (dq1 dq2 : dfrac) Pq Pq' :
    IsIncludedMerge (Some dq1) (Some dq2) M Pq →
    MakeAnd Pq (a1 ≡ a2) Pq' →
    IsIncludedMerge (●{dq1} a1) (●{dq2} a2 ⋅ ◯ a3) M Pq'.
  Proof.
    rewrite /IsIncludedMerge /MakeAnd => Hdq <-.
    iIntros "#Ha2".
    iSplit.
    - iIntros "#Hi".
      rewrite view_includedI /=.
      iDestruct ("Hi" with "Ha2") as "(_ & Hdq & Ha1)"; iClear "Hi".
      rewrite !is_included_merge'.
      rewrite bi.intuitionistically_and.
      rewrite auth_both_dfrac_validI.
      iDestruct "Ha2" as "(% & Hai & Ha2)".
      iSplit; first by iApply Hdq => //.
      iApply "Ha1" => //.
    - iIntros "[#Hpq #Has]". iRewrite "Has"; iClear "Has".
      rewrite auth_both_dfrac_validI. iDestruct "Ha2" as "(% & _ & Ha2)".
      iAssert (Some dq1 ≼ Some dq2)%I as "#[%dq Hqs]".
      { iApply Hdq => //. }
      destruct dq as [q|].
      * iExists (●{q} a2 ⋅ ◯ a3).
        rewrite view_equivI /= !left_id !right_id. iSplit => //.
        rewrite -!Some_op -pair_op.
        rewrite !option_equivI prod_equivI /= agree_idemp. iSplit => //.
      * rewrite right_id option_equivI.
        iRewrite "Hqs".
        by iExists (◯ a3).
  Qed.

  Global Instance auth_frag_auth_frag_included {A : ucmra} (a1 a2 a3 a4 : A) (dq1 dq2 : dfrac) Pq Pa Pr' Pr :
    IsIncludedMerge (Some dq1) (Some dq2) M Pq →
    IsIncludedMerge a4 a3 M Pa →
    MakeAnd Pq (a1 ≡ a2) Pr' →
    MakeAnd Pr' Pa Pr →
    IsIncludedMerge (●{dq1} a1 ⋅ ◯ a4) (●{dq2} a2 ⋅ ◯ a3) M Pr.
  Proof.
    rewrite /IsIncludedMerge /MakeAnd => HPq HPa <- <-.
    iIntros "#Ha2".
    iSplit.
    - iIntros "#Hi".
      rewrite view_includedI /=.
      iDestruct ("Hi" with "Ha2") as "(Ha4 & Hdq & Ha1)"; iClear "Hi".
      rewrite !is_included_merge' !left_id.
      rewrite !bi.intuitionistically_and.
      rewrite auth_both_dfrac_validI.
      iDestruct "Ha2" as "(% & [%c Hac] & Ha2)".
      iSplit; try iSplit.
      * iApply HPq => //.
      * iApply "Ha1" => //.
      * iApply HPa => //.
        iApply uPred.cmra_valid_weaken. iRevert "Ha2". iRewrite "Hac". eauto.
    - iIntros "#[[#Hpq #Has] HPa]". iRewrite "Has"; iClear "Has".
      rewrite auth_both_dfrac_validI. iDestruct "Ha2" as "(% & [%c Hac] & Ha2)".
      iAssert (Some dq1 ≼ Some dq2)%I as "#[%dq Hqs]"; last iClear "Hpq".
      { iApply HPq => //. }
      iAssert (a4 ≼ a3)%I as "#[%c' Hc]"; last iClear "HPa".
      { iApply HPa => //.
        iApply uPred.cmra_valid_weaken. iRevert "Ha2". iRewrite "Hac". eauto. }
      destruct dq as [q|].
      * iExists (●{q} a2 ⋅ ◯ c').
        rewrite view_equivI /= !left_id !right_id. iSplit => //.
        rewrite -!Some_op -pair_op.
        rewrite !option_equivI prod_equivI /= agree_idemp. iSplit => //.
      * rewrite right_id option_equivI.
        iRewrite "Hqs".
        iExists (◯ c'). rewrite view_equivI /= right_id !left_id. eauto.
  Qed.

  Global Instance auth_frag_included {A : ucmra} (a1 a2 : A) (dq2 : dfrac) :
    IsIncludedMerge (●{dq2} a2) (◯ a1) M False.
  Proof.
    rewrite /IsIncludedMerge.
    iIntros "#Ha2".
    iSplit => //.
    iIntros "#Hi".
    rewrite view_includedI /=.
    iDestruct ("Hi" with "Ha2") as "[_ $]".
  Qed.

  Lemma frag_frag_included {A : ucmra} (a1 a2 : A) Pq :
    IsIncludedMerge a1 a2 M Pq →
    IsIncludedMerge (◯ a1) (◯ a2) M Pq.
  Proof.
    rewrite /IsIncludedMerge => HPq.
    iIntros "#Ha2".
    iSplit => //.
    - iIntros "#Hi".
      rewrite view_includedI /=.
      iDestruct ("Hi" with "Ha2") as "[Ha1a2 _]".
      iApply HPq => //.
      rewrite auth_frag_validI //.
    - iIntros "#HPq".
      iAssert (a1 ≼ a2)%I as "[%a Ha]".
      { iApply HPq => //. rewrite auth_frag_validI //. }
      iExists (◯ a).
      rewrite -auth_frag_op view_equivI /=.
      iSplit => //.
  Qed.

End auth_inclusion. *)