From iris.prelude Require Import options.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.

Definition step_gen `{!irisGS_gen hlc Λ Σ} E P : iProp Σ :=
  ∀ σ n κ κs nt,
    state_interp σ n (κ ++ κs) nt ={E}=∗ state_interp σ n (κ ++ κs) nt ∗
    (P σ n κ κs nt).

Local Definition step_get_def `{!irisGS_gen hlc Λ Σ} E (P : iProp Σ) : iProp Σ :=
  step_gen E (λ _ _ _ _ _, |={E}=> P)%I.
Local Definition step_get_aux : seal (@step_get_def).
Proof. by eexists. Qed.
Definition step_get := step_get_aux.(unseal).
Global Arguments step_get {hlc Λ Σ _}.
Local Lemma step_get_unseal `{!irisGS_gen hlc Λ Σ} : step_get = step_get_def.
Proof. rewrite -step_get_aux.(seal_eq) //. Qed.

Notation "|~{ E }~| P" := (step_get E P)%I
  (at level 99, P at level 200, format "'[  ' |~{  E  }~|  '/' P ']'").
Notation "|~~| P" := (|~{∅}~| P)%I
  (at level 99, P at level 200, format "'[  ' |~~|  '/' P ']'").

Local Definition step_update_def `{!irisGS_gen hlc Λ Σ} E (P : iProp Σ) : iProp Σ :=
  step_gen E (λ σ1 n κ κs nt,
                (|={∅}▷=>^(S (num_laters_per_step n))
                   ∀ σ2 nt', (state_interp σ2 (S n) κs (nt' + nt) ={E}=∗
                              state_interp σ2 (S n) κs (nt' + nt) ∗ P)))%I.
Local Definition step_update_aux : seal (@step_update_def).
Proof. by eexists. Qed.
Definition step_update := step_update_aux.(unseal).
Global Arguments step_update {hlc Λ Σ _}.
Local Lemma step_update_unseal `{!irisGS_gen hlc Λ Σ} :
  step_update = step_update_def.
Proof. rewrite -step_update_aux.(seal_eq) //. Qed.

Notation "|~{ E }~> P" := (step_update E P)%I
  (at level 99, P at level 200, format "'[  ' |~{  E  }~>  '/' P ']'").
Notation "|~~> P" := (|~{∅}~> P)%I
  (at level 99, P at level 200, format "'[  ' |~~>  '/' P ']'").

Section with_Σ.
  Context `{!irisGS_gen hlc Λ Σ}.

  Lemma step_fupdN_empty_sep n (R Q : iProp Σ) :
    (|={∅}▷=>^n R) ∗ (|={∅}▷=>^n Q) -∗ |={∅}▷=>^n (R ∗ Q).
  Proof.
    induction n as [|n IH]; simpl; [done|].
    iIntros "[HR HQ]". iApply IH.
    iMod "HR". iMod "HQ". iIntros "!>!>". iMod "HR". iMod "HQ". by iFrame.
  Qed.

  Lemma wp_step_get s E e P Φ :
    TCEq (to_val e) None →
    (|~{E}~| P) -∗
    (P -∗ WP e @ s; E {{ Φ }}) -∗
    WP e @ s; E {{ Φ }}.
  Proof.
    rewrite step_get_unseal.
    iIntros (Hval) "HP Hwp". rewrite !wp_unfold /wp_pre /=.
    destruct (to_val e); [by inversion Hval|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iMod "HP".
    by iDestruct ("Hwp" with "HP Hσ") as "Hwp".
  Qed.

  Lemma step_get_intro E P :
    P -∗ |~{E}~| P.
  Proof. rewrite step_get_unseal. iIntros "HP" (σ n κ κs nt) "Hσ". by iFrame. Qed.

  Lemma step_get_comm E P Q :
    (|~{E}~| P) -∗ (|~{E}~| Q) -∗ |~{E}~| P ∗ Q.
  Proof.
    rewrite step_get_unseal.
    iIntros "HP HQ" (σ n κ κs nt) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iMod ("HQ" with "Hσ") as "[Hσ HQ]".
    iMod "HP". iMod "HQ". by iFrame.
  Qed.

  Lemma step_get_mono E P Q :
    (P -∗ Q) -∗ (|~{E}~| P) -∗ |~{E}~| Q.
  Proof.
    rewrite step_get_unseal.
    iIntros "HPQ HP" (σ n κ κs nt) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]". iIntros "!>". iFrame. by iApply "HPQ".
  Qed.

  Lemma fupd_step_get_fupd E P : (|={E}=> |~{E}~| |={E}=> P) -∗ |~{E}~| P.
  Proof.
    rewrite step_get_unseal.
    iIntros "Hstep" (σ n κ κs nt) "Hσ".
    iMod "Hstep". iMod ("Hstep" with "Hσ") as "[Hσ Hstep]".
    iIntros "!>". iFrame=> /=.
    by iMod "Hstep".
  Qed.

  Lemma step_get_fupd E P : (|~{E}~| |={E}=> P) -∗ |~{E}~| P.
  Proof. iIntros "HP". iApply fupd_step_get_fupd. by iModIntro. Qed.

  Lemma fupd_step_get E P : (|={E}=> |~{E}~| P) -∗ |~{E}~| P.
  Proof.
    iIntros "HP". iApply fupd_step_get_fupd. iMod "HP".
    iModIntro. iApply (step_get_mono with "[] HP"). by iIntros "HP!>".
  Qed.

  Global Instance step_get_except0 E P : IsExcept0 (|~{E}~| P).
  Proof.
    rewrite /IsExcept0. iIntros "Hstep". iApply fupd_step_get.
    iApply is_except_0. by iMod "Hstep".
  Qed.

  Lemma wp_step_update s E e P Φ :
    TCEq (to_val e) None →
    (|~{E}~> P) -∗
    WP e @ s; E {{ v, P ={E}=∗ Φ v }} -∗
    WP e @ s; E {{ Φ }}.
  Proof.
    rewrite step_update_unseal.
    iIntros (Hval) "Hstep Hwp". rewrite !wp_unfold /wp_pre /=.
    destruct (to_val e); [by inversion Hval|].
    iIntros (σ1 n κ κs nt) "Hσ".
    iMod ("Hstep" with "Hσ") as "[Hσ Hstep]"=> /=.
    iMod ("Hwp" with "Hσ") as "[% Hwp]". iMod "Hstep".
    iModIntro. iSplit; [done|].
    iIntros (e2 σ2 efs Hstep) "H£".
    iMod ("Hwp" with "[//] H£") as "Hwp". iIntros "!> !>".
    iMod "Hstep". iMod "Hwp". iIntros "!>".
    iAssert (|={∅}▷=>^(num_laters_per_step n) _ ∗ _)%I
      with "[Hwp Hstep]" as "Hwp".
    { iApply step_fupdN_empty_sep. iFrame. }
    iApply (step_fupdN_wand with "Hwp").
    iIntros "[Hstep Hwp]". iMod "Hwp" as "(Hσ & Hwp & Hwps)".
    iMod ("Hstep" with "Hσ") as "[Hσ HP]".
    iModIntro. iFrame.
    iApply (wp_strong_mono with "Hwp"); [done|done|..].
    iIntros (v) "H". by iApply ("H").
  Qed.

  Lemma step_update_later E P :
    ▷ P -∗ |~{E}~> P.
  Proof.
    rewrite step_update_unseal.
    iIntros "HP". iIntros (σ n κ κs nt) "Hσ".
    iFrame. iApply step_fupdN_intro; [set_solver|].
    iIntros "!>!>!>" (σ2 nt') "Hσ". by iFrame.
  Qed.

  Lemma step_update_intro E P : P -∗ |~{E}~> P.
  Proof. iIntros "HP". by iApply step_update_later. Qed.

  Lemma step_update_comm E P Q :
    (|~{E}~> P) -∗ (|~{E}~> Q) -∗ |~{E}~> P ∗ Q.
  Proof.
    rewrite step_update_unseal.
    iIntros "HP HQ". iIntros (σ n κ κs nt) "Hσ".
    iDestruct ("HP" with "Hσ") as "HP".
    iMod "HP" as "[Hσ HP]".
    iMod ("HQ" with "Hσ") as "[Hσ HQ]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iMod "HQ". iIntros "!>!>". iMod "HP". iMod "HQ". iIntros "!>".
    iDestruct (step_fupdN_empty_sep with "[$HP $HQ]") as "HPQ".
    iApply (step_fupdN_wand with "[HPQ]"); first by iApply "HPQ".
    iIntros "[HP HQ]" (σ2 nt') "Hσ".
    iMod ("HQ" with "Hσ") as "[Hσ HQ]".
    iDestruct ("HP" with "Hσ") as "HP".
    iMod "HP". by iFrame.
  Qed.

  Lemma step_update_mono E P Q : (P -∗ Q) -∗ (|~{E}~> P) -∗ |~{E}~> Q.
  Proof.
    rewrite step_update_unseal.
    iIntros "HPQ HP". iIntros (σ n κ κs nt) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iIntros "!>!>". iMod "HP". iIntros "!>".
    iAssert (|={∅}▷=>^(num_laters_per_step n) _ ∗ _)%I with "[HPQ HP]" as "H".
    { iApply step_fupdN_frame_l. iFrame. iExact "HPQ". }
    iApply (step_fupdN_wand with "H").
    iIntros "[HPQ HP]" (??) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iDestruct ("HPQ" with "HP") as "HQ".
    by iFrame.
  Qed.

  Lemma fupd_step_update_fupd E P : (|={E}=> |~{E}~> |={E}=> P) -∗ |~{E}~> P.
  Proof.
    rewrite step_update_unseal.
    iIntros "Hstep" (σ n κ κs nt) "Hσ".
    iMod "Hstep". iMod ("Hstep" with "Hσ") as "[Hσ Hstep]".
    iIntros "!>". iFrame=> /=.
    iMod "Hstep". iIntros "!>!>". iMod "Hstep". iIntros "!>".
    iApply (step_fupdN_wand with "Hstep").
    iIntros "Hstep" (??) "Hσ".
    iMod ("Hstep" with "Hσ") as "[Hσ Hstep]".
    iMod "Hstep". iModIntro. by iFrame.
  Qed.

  Lemma step_update_fupd E P : (|~{E}~> |={E}=> P) -∗ |~{E}~> P.
  Proof. iIntros "HP". iApply fupd_step_update_fupd. by iModIntro. Qed.

  Lemma fupd_step_update E P : (|={E}=> |~{E}~> P) -∗ |~{E}~> P.
  Proof.
    iIntros "HP". iApply fupd_step_update_fupd. iMod "HP".
    iModIntro. iApply (step_update_mono with "[] HP"). by iIntros "HP!>".
  Qed.

  Global Instance step_update_except0 E P : IsExcept0 (|~{E}~> P).
  Proof.
    rewrite /IsExcept0. iIntros "Hstep". iApply fupd_step_update.
    iApply is_except_0. by iMod "Hstep".
  Qed.

End with_Σ.

Section with_Σ.
  Context `{iG : irisGS_gen hlc Λ Σ}.

  Class IntoPreStep E (P Q : iProp Σ) := into_pre_step : P ⊢ |~{E}~| Q.
  Global Instance into_pre_step_id E P : IntoPreStep E (|~{E}~| P) P | 0.
  Proof. rewrite /IntoPreStep. by iIntros "HP". Qed.
  Global Instance into_pre_step_intro E P : IntoPreStep E P P | 1.
  Proof. rewrite /IntoPreStep. by iApply step_get_intro. Qed.

  Lemma modality_pre_step_mixin E :
    modality_mixin (@step_get hlc Λ Σ iG E)
                   (MIEnvId) (MIEnvTransform (IntoPreStep E)).
  Proof.
    split; simpl.
    - iIntros (P). by iApply step_get_intro.
    - rewrite /IntoPreStep. iIntros (P Q HPQ) "HP". by iApply HPQ.
    - iIntros "H". by iApply step_get_intro.
    - iIntros (P Q HPQ) "HP". iApply (step_get_mono with "[] HP"). iApply HPQ.
    - iIntros (P Q) "[HP HQ]".
      by iDestruct (step_get_comm with "HP HQ") as "HPQ".
  Qed.
  Definition modality_pre_step E :=
    Modality _ (modality_pre_step_mixin E).
  Global Instance from_modality_pre_step E P :
    FromModal True (modality_pre_step E) (|~{E}~| P) (|~{E}~| P) P.
  Proof. by rewrite /FromModal /=. Qed.

  Global Instance elim_modal_pre_step_fupd p E P Q :
    ElimModal True p false (|={E}=> P) P (|~{E}~| Q) (|~{E}~| Q).
  Proof.
    destruct p.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]". iDestruct "HP" as "#HP".
      iApply fupd_step_get. iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
      by iIntros "!>!>".
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]".
      iApply fupd_step_get. iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
      by iIntros "!>!>".
  Qed.

  Global Instance elim_modal_pre_step_bupd p E P Q :
    ElimModal True p false (|==> P) P (|~{E}~| Q) (|~{E}~| Q).
  Proof.
    destruct p.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]". iDestruct "HP" as "#HP".
      iApply fupd_step_get. iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
      by iIntros "!>!>".
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]".
      iApply fupd_step_get. iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
      by iIntros "!>!>".
  Qed.

  Class IntoStep E (P Q : iProp Σ) := into_step : P ⊢ |~{E}~> Q.
  Global Instance into_step_id E P : IntoStep E (|~{E}~> P) P | 0.
  Proof. rewrite /IntoStep. by iIntros "HP". Qed.
  Global Instance into_step_intro E P : IntoStep E P P | 1.
  Proof. rewrite /IntoStep. by iApply step_update_intro. Qed.

  Lemma modality_step_mixin E :
    modality_mixin (@step_update hlc Λ Σ iG E)
                   (MIEnvId) (MIEnvTransform (IntoStep E)).
  Proof.
    split; simpl.
    - iIntros (P). by iApply step_update_intro.
    - rewrite /IntoStep. iIntros (P Q HPQ) "HP". by iApply HPQ.
    - iIntros "H". by iApply step_update_intro.
    - iIntros (P Q HPQ) "HP". iApply (step_update_mono with "[] HP"). iApply HPQ.
    - iIntros (P Q) "[HP HQ]".
      by iDestruct (step_update_comm with "HP HQ") as "HPQ".
  Qed.
  Definition modality_step E :=
    Modality _ (modality_step_mixin E).
  Global Instance from_modality_step E P :
    FromModal True (modality_step E) (|~{E}~> P) (|~{E}~> P) P.
  Proof. by rewrite /FromModal /=. Qed.

  Global Instance elim_modal_step_bupd p E P Q :
    ElimModal True p false (|==> P) P (|~{E}~> Q) (|~{E}~> Q).
  Proof.
    destruct p.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]". iDestruct "HP" as "#HP".
      iApply fupd_step_update. iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
      by iIntros "!>!>".
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]".
      iApply fupd_step_update. iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
      by iIntros "!>!>".
  Qed.

  Global Instance elim_modal_step_fupd p E P Q :
    ElimModal True p false (|={E}=> P) P (|~{E}~> Q) (|~{E}~> Q).
  Proof.
    destruct p.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]". iDestruct "HP" as "#HP".
      iApply fupd_step_update. iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
      by iIntros "!>!>".
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]".
      iApply fupd_step_update. iMod "HP". iDestruct ("HPQ" with "HP") as "HQ".
      by iIntros "!>!>".
  Qed.

End with_Σ.

Example step_get_example `{irisGS_gen hlc Λ Σ} E (P Q : iProp Σ) :
  (|~{E}~| P) -∗ (|==> P ==∗ Q) -∗ |~{E}~| Q.
Proof.
  iIntros "HP HPQ". iMod "HPQ". iApply step_get_fupd.
  iIntros "!>". by iMod ("HPQ" with "HP").
Qed.

Example step_update_example `{irisGS_gen hlc Λ Σ} E (P Q : iProp Σ) :
  (|~{E}~> P) -∗ (|==> P ==∗ Q) -∗ |~{E}~> Q.
Proof.
  iIntros "HP HPQ". iMod "HPQ". iApply step_update_fupd.
  iIntros "!>". by iMod ("HPQ" with "HP").
Qed.
