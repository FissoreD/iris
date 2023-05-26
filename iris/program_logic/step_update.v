From iris.prelude Require Import options.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.

Local Definition step_get_def `{!irisGS_gen hlc Λ Σ} E (P : iProp Σ) : iProp Σ :=
  ∀ e s Φ,
    ⌜TCEq (to_val e) None⌝ →
    (P ={E}=∗ WP e @ s; E {{ v, Φ v }}) -∗
    WP e @ s; E {{ Φ }}.
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
  ∀ e s Φ,
    ⌜TCEq (to_val e) None⌝ →
    WP e @ s; E {{ v, P ={E}=∗ Φ v }} -∗
    WP e @ s; E {{ Φ }}.
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

  Lemma wp_step_get s E e P Φ :
    TCEq (to_val e) None →
    (|~{E}~| P) -∗
    (P ={E}=∗ WP e @ s; E {{ Φ }}) -∗
    WP e @ s; E {{ Φ }}.
  Proof.
    rewrite step_get_unseal.
    iIntros (Hval) "HP Hwp". by iApply ("HP" with "[] Hwp").
  Qed.

  Lemma step_get_intro E P :
    P -∗ |~{E}~| P.
  Proof.
    rewrite step_get_unseal.
    iIntros "HP". iIntros (s e Φ Hval) "Hwp". by iMod ("Hwp" with "HP").
  Qed.

  Lemma step_get_comm E P Q :
    (|~{E}~| P) -∗ (|~{E}~| Q) -∗ |~{E}~| P ∗ Q.
  Proof.
    rewrite step_get_unseal.
    iIntros "HP HQ".
    iIntros (s e Φ Hval) "HPQ".
    iApply "HP"; [done|]. iIntros "HP!>".
    iApply "HQ"; [done|]. iIntros "HQ!>".
    iMod ("HPQ" with "[HP HQ]"); [iFrame|done].
  Qed.

  Lemma step_get_mono E P Q :
    (P -∗ Q) -∗ (|~{E}~| P) -∗ |~{E}~| Q.
  Proof.
    rewrite step_get_unseal.
    iIntros "HPQ Hstep".
    iIntros (s e Φ Hval) "Hwp".
    iApply "Hstep"; [done|].
    iIntros "HP!>".
    iDestruct ("HPQ" with "HP") as "HQ".
    by iMod ("Hwp" with "HQ").
  Qed.

  Lemma fupd_step_get_fupd E P : (|={E}=> |~{E}~| |={E}=> P) -∗ |~{E}~| P.
  Proof.
    rewrite step_get_unseal.
    iIntros "Hstep".
    iIntros (s e Φ Hval) "Hwp".
    iMod "Hstep". iApply "Hstep"; [done|].
    iMod 1 as "HP". by iMod ("Hwp" with "HP").
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
    iIntros (Hval) "Hstep Hwp".
    by iApply "Hstep".
  Qed.

  Lemma step_update_later E P :
    ▷ P -∗ |~{E}~> P.
  Proof.
    rewrite step_update_unseal.
    iIntros "HP".
    iIntros (e s Φ Hval) "Hwp".
    iApply (wp_step_fupd with "[HP]"); [set_solver| |].
    { iIntros "!>!>!>". iExact "HP". }
    done.
  Qed.

  Lemma step_update_intro E P : P -∗ |~{E}~> P.
  Proof. iIntros "HP". by iApply step_update_later. Qed.

  Lemma step_update_comm E P Q :
    (|~{E}~> P) -∗ (|~{E}~> Q) -∗ |~{E}~> P ∗ Q.
  Proof.
    rewrite step_update_unseal.
    iIntros "HP HQ".
    iIntros (e s Φ Hval) "Hwp".
    iApply "HQ"; [done|]. iApply "HP"; [done|].
    iApply (wp_mono with "Hwp").
    iIntros (v) "HPQ". iIntros "HP !> HQ". iApply "HPQ". iFrame.
  Qed.

  Lemma step_update_mono E P Q : (P -∗ Q) -∗ (|~{E}~> P) -∗ |~{E}~> Q.
  Proof.
    rewrite step_update_unseal.
    iIntros "HPQ HP".
    iIntros (e s Φ Hval) "Hwp".
    iApply "HP"; [done|].
    iApply (wp_wand with "Hwp").
    iIntros (v) "HΦ HP". iDestruct ("HPQ" with "HP") as "HQ".
    by iMod ("HΦ" with "HQ").
  Qed.

  Lemma fupd_step_update_fupd E P : (|={E}=> |~{E}~> |={E}=> P) -∗ |~{E}~> P.
  Proof.
    rewrite step_update_unseal.
    iIntros "Hstep".
    iIntros (e s Φ Hval) "Hwp".
    iMod "Hstep".
    iApply "Hstep"; [done|].
    iApply (wp_mono with "Hwp").
    iIntros (v) "HΦ HP". iMod "HP". by iMod ("HΦ" with "HP").
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
