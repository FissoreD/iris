From iris.prelude Require Import options.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.

Section with_Σ.
  Context `{!irisGS_gen hlc Λ Σ}.

  Lemma step_fupdN_empty_sep n (R Q : iProp Σ) :
    (|={∅}▷=>^n R) ∗ (|={∅}▷=>^n Q) -∗ |={∅}▷=>^n (R ∗ Q).
  Proof.
    induction n as [|n IH]; simpl; [done|].
    iIntros "[HR HQ]". iApply IH.
    iMod "HR". iMod "HQ". iIntros "!>!>". iMod "HR". iMod "HQ". by iFrame.
  Qed.

  Definition step_get E1 E2 P : iProp Σ :=
    ∀ σ n κ κs nt, state_interp σ n (κ ++ κs) nt ={E1,E2}=∗ state_interp σ n (κ ++ κs) nt ∗
                 (P σ n κ κs nt).

  Notation "|~{ E1 , E2 }~| P" := (step_get E1 E2 (λ _ _ _ _ _, |={E2,E1}=> P))%I
    (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~|  '/' P ']'").
  Notation "|~{ E }~| P" := (|~{E,∅}~| P)
    (at level 99, P at level 200, format "'[  ' |~{  E  }~|  '/' P ']'").
  Notation "|~~| P" := (|~{∅}~| P)
    (at level 99, P at level 200, format "'[  ' |~~|  '/' P ']'").

  Lemma wp_step_get s E e P Φ :
    TCEq (to_val e) None →
    (|~{E}~| P) -∗
    (P -∗ WP e @ s; E {{ Φ }}) -∗
    WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hval) "HP Hwp". rewrite !wp_unfold /wp_pre /=.
    destruct (to_val e); [by inversion Hval|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]". iMod "HP".
    by iDestruct ("Hwp" with "HP Hσ") as "Hwp".
  Qed.

  Lemma step_get_intro E P :
    P -∗ |~{E}~| P.
  Proof.
    iIntros "HP" (σ n κ κs nt) "Hσ". iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose". by iFrame.
  Qed.

  Lemma step_get_open E1 E2 E3 P :
    (|={E1,E2}=> |~{E2,E3}~| (|={E2, E1}=> P)) -∗ |~{E1,E3}~| P.
  Proof.
    iIntros "Hstep" (σ n κ κs nt) "Hσ".
    iMod "Hstep". iMod ("Hstep" with "Hσ") as "[Hσ Hstep]".
    iIntros "!>". iFrame=> /=. by iMod "Hstep".
  Qed.

  Lemma step_get_comm E P Q :
    (|~{E}~| P) -∗ (|~{E}~| Q) -∗ |~{E}~| P ∗ Q.
  Proof.
    iIntros "HP HQ" (σ n κ κs nt) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]". iMod "HP".
    iMod ("HQ" with "Hσ") as "[Hσ HQ]". iMod "HQ".
    iFrame. iApply fupd_mask_intro; [set_solver|]. by iMod 1.
  Qed.

  (* TODO: Not sure what to call this. *)
  Lemma step_get_impl E P Q :
    (|~{E}~| P) -∗ (P -∗ |~{E}~| Q) -∗ |~{E}~| Q.
  Proof.
    iIntros "HP HPQ" (σ n κ κs nt) "Hσ". iMod ("HP" with "Hσ") as "[Hσ HP]".
    iMod "HP". by iMod ("HPQ" with "HP Hσ") as "HPQ".
  Qed.

  Lemma step_get_mono E P Q :
    (P -∗ Q) -∗ (|~{E}~| P) -∗ |~{E}~| Q.
  Proof.
    iIntros "HPQ HP". iApply (step_get_impl with "HP").
    iIntros "HP". iApply step_get_intro. by iApply "HPQ".
  Qed.

  Definition step_update E1 E2 P : iProp Σ :=
    step_get E1 E2 (λ σ1 n κ κs nt,
                      (|={∅}▷=>^(S (num_laters_per_step n))
                         ∀ σ2 nt', (state_interp σ2 (S n) κs (nt' + nt) ={E2,E1}=∗
                                    state_interp σ2 (S n) κs (nt' + nt) ∗ P)))%I.
  Notation "|~{ E1 , E2 }~> P" := (step_update E1 E2 P)
    (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~>  '/' P ']'").
  Notation "|~{ E }~> P" := (step_update E ∅ P)
    (at level 99, P at level 200, format "'[  ' |~{  E  }~>  '/' P ']'").
  Notation "|~~> P" := (|~{∅}~> P)
    (at level 99, P at level 200, format "'[  ' |~~>  '/' P ']'").

  Lemma wp_step_update_strong s E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (|~{E1,E2}~> P) -∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗
    WP e @ s; E1 {{ Φ }}.
  Proof.
    iIntros (Hval HE) "Hstep Hwp". rewrite !wp_unfold /wp_pre /=.
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

  Lemma step_get_step_update E1 E2 P Q :
    (|~{E1}~| P) -∗
    (P -∗ |~{E1,E2}~> Q) -∗
    |~{E1,E2}~> Q.
  Proof.
    iIntros "HP HPQ" (σ n κ κs nt) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]". iMod "HP".
    iMod ("HPQ" with "HP Hσ") as "[Hσ HPQ]". by iFrame.
  Qed.

  Lemma step_update_frame E1 E2 Ef P :
    E2 ⊆ E1 → E1 ## Ef →
    (|~{E1,E2}~> P) -∗
    (|~{E1 ∪ Ef,E2 ∪ Ef}~> P).
  Proof.
    iIntros (Hle Hidjs) "Hstep".
    iIntros (σ n κ κs nt) "Hσ".
    iDestruct ("Hstep" with "Hσ") as "Hstep".
    iDestruct (fupd_mask_frame_r E1 E2 Ef with "Hstep") as "Hstep"; [done|].
    iMod "Hstep" as "[Hσ Hstep]".
    iApply fupd_mask_intro; [done|].
    iIntros "Hclose".
    iFrame=> /=.
    iMod "Hstep". iIntros "!>!>". iMod "Hstep". iIntros "!>".
    iApply (step_fupdN_wand with "Hstep").
    iIntros "Hstep" (σ2 nt') "Hσ".
    iDestruct ("Hstep" with "Hσ") as "Hstep".
    iMod "Hclose".
    iApply fupd_mask_frame_r; [set_solver|].
    iMod "Hstep".
    iModIntro. done.
  Qed.

  Lemma wp_step_update s E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (|~{E1∖E2}~> P) -∗
    WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗
    WP e @ s; E1 {{ Φ }}.
  Proof.
    iIntros (Hval HE) "Hstep Hwp".
    iDestruct (step_update_frame (E1∖E2) ∅ (E2) with "Hstep") as "Hstep";
      [set_solver|set_solver|].
    replace (E1 ∖ E2 ∪ E2) with E1; last first.
    { rewrite difference_union_L. set_solver. }
    replace (∅ ∪ E2) with E2 by set_solver.
    by iApply (wp_step_update_strong with "Hstep").
  Qed.

  Lemma step_update_intro E1 E2 P :
    E2 ⊆ E1 → P -∗ |~{E1,E2}~> P.
  Proof.
    iIntros (HE) "HP". iIntros (σ n κ κs nt) "Hσ". iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose". iFrame. iApply step_fupdN_intro; [set_solver|].
    iIntros "!>!>" (σ2 nt') "Hσ". iMod "Hclose". iFrame. done.
  Qed.

  Lemma step_update_frame_l E1 E2 P Q :
    (|~{E1,E2}~> P) -∗ (|={E1}=> Q) -∗ |~{E1,E2}~> (P ∗ Q).
  Proof.
    iIntros "HP HQ" (σ n κ κs nt) "Hσ".
    iMod "HQ". iMod ("HP" with "Hσ") as "[Hσ HP]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iIntros "!>!>". iMod "HP". iIntros "!>".
    iApply (step_fupdN_wand with "HP").
    iIntros "HP" (σ2 nt') "Hσ". iMod ("HP" with "Hσ") as "[Hσ HP]". by iFrame.
  Qed.

  Lemma step_update_comm E1 E2 P Q :
    E1 ## E2 → (|~{E1}~> P) -∗ (|~{E2}~> Q) -∗ |~{E1 ∪ E2}~> P ∗ Q.
  Proof.
    iIntros (HE) "HP HQ". iIntros (σ n κ κs nt) "Hσ".
    iDestruct ("HP" with "Hσ") as "HP".
    iDestruct (fupd_mask_frame_r E1 ∅ E2 with "HP") as "HP"; [done|].
    iMod "HP" as "[Hσ HP]". rewrite union_empty_l_L.
    iMod ("HQ" with "Hσ") as "[Hσ HQ]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iMod "HQ". iIntros "!>!>". iMod "HP". iMod "HQ". iIntros "!>".
    iDestruct (step_fupdN_empty_sep with "[$HP $HQ]") as "HPQ".
    iApply (step_fupdN_wand with "[HPQ]"); first by iApply "HPQ".
    iIntros "[HP HQ]" (σ2 nt') "Hσ".
    iMod ("HQ" with "Hσ") as "[Hσ HQ]".
    iDestruct ("HP" with "Hσ") as "HP".
    iDestruct (fupd_mask_frame_r ∅ E1 E2 with "HP") as "HP"; [set_solver|].
    rewrite union_empty_l_L.
    iMod "HP". iFrame. done.
  Qed.

  (* TODO: Not sure if this is important to keep *)
  Lemma step_update_impl E1 E2 P Q :
    (|~{E2,E2}~> P) -∗ (|~{E1,E2}~> P -∗ Q) -∗ |~{E1,E2}~> Q.
  Proof.
    iIntros "HP HPQ" (σ n κ κs nt) "Hσ".
    iMod ("HPQ" with "Hσ") as "[Hσ HPQ]".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iMod "HPQ". iIntros "!>!>". iMod "HP". iMod "HPQ". iIntros "!>".
    iAssert (|={∅}▷=>^(num_laters_per_step n) _ ∗ _)%I with "[HPQ HP]" as "H".
    { iApply step_fupdN_empty_sep. iFrame. }
    iApply (step_fupdN_wand with "H").
    iIntros "[HP HPQ]" (σ2 nt') "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iMod ("HPQ" with "Hσ") as "[Hσ HPQ]".
    iFrame. by iApply "HPQ".
  Qed.

  Lemma step_update_mono E1 E2 E3 P Q :
    E1 ⊆ E2 → (|~{E1,E3}~> P) -∗ (P ={E1,E2}=∗ Q) -∗ |~{E2,E3}~> Q.
  Proof.
    iIntros (Hle) "HP HPQ". iIntros (σ n κ κs nt) "Hσ".
    iApply fupd_mask_weaken; [done|]. iIntros "Hclose".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iIntros "!>". iFrame=> /=.
    iMod "HP". iIntros "!>!>". iMod "HP". iIntros "!>".
    iAssert (|={∅}▷=>^(num_laters_per_step n) _ ∗ _)%I with "[HPQ HP]" as "H".
    { iApply step_fupdN_frame_l. iFrame. iExact "HPQ". }
    iApply (step_fupdN_wand with "H").
    iIntros "[HPQ HP]" (??) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iMod ("HPQ" with "HP") as "HQ".
    by iFrame.
  Qed.

  Lemma step_update_open E1 E2 E3 P :
    (|={E1,E2}=> |~{E2,E3}~> (|={E2, E1}=> P)) -∗ |~{E1,E3}~> P.
  Proof.
    iIntros "Hstep" (σ n κ κs nt) "Hσ".
    iMod "Hstep". iMod ("Hstep" with "Hσ") as "[Hσ Hstep]".
    iIntros "!>". iFrame=> /=.
    iMod "Hstep". iIntros "!>!>". iMod "Hstep". iIntros "!>".
    iApply (step_fupdN_wand with "Hstep").
    iIntros "Hstep" (??) "Hσ".
    iMod ("Hstep" with "Hσ") as "[Hσ Hstep]".
    iMod "Hstep". iModIntro. by iFrame.
  Qed.

End with_Σ.

Notation "|~{ E1 , E2 }~| P" := (step_get E1 E2 (λ _ _ _ _ _, |={E2,E1}=> P))%I (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~|  '/' P ']'").
Notation "|~{ E }~| P" := (|~{E,∅}~| P) (at level 99, P at level 200, format "'[  ' |~{  E  }~|  '/' P ']'").
Notation "|~~| P" := (|~{∅}~| P) (at level 99, P at level 200, format "'[  ' |~~|  '/' P ']'").

Notation "|~{ E1 , E2 }~> P" := (step_update E1 E2 P) (at level 99, P at level 200, format "'[  ' |~{  E1  ,  E2  }~>  '/' P ']'").
Notation "|~{ E }~> P" := (step_update E ∅ P) (at level 99, P at level 200, format "'[  ' |~{  E  }~>  '/' P ']'").
Notation "|~~> P" := (|~{∅}~> P) (at level 99, P at level 200, format "'[  ' |~~>  '/' P ']'").

Section with_Σ.
  Context `{iG : irisGS_gen hlc Λ Σ}.

  Class IntoStep (P Q : iProp Σ) :=
    into_step : P ⊢ |~~> Q.
  Instance into_step_id P: IntoStep (|~~> P) P | 0.
  Proof. rewrite /IntoStep. by iIntros "HP". Qed.
  Instance into_step_intro P: IntoStep P P | 1.
  Proof. rewrite /IntoStep. by iApply step_update_intro. Qed.

  Lemma modality_step_mixin :
    modality_mixin (@step_update hlc Λ Σ iG ∅ ∅)
                   (MIEnvId) (MIEnvTransform IntoStep).
  Proof.
    split; simpl.
    - iIntros (P). by iApply step_update_intro.
    - rewrite /IntoStep. iIntros (P Q HPQ) "HP". by iApply HPQ.
    - iIntros "H". by iApply step_update_intro.
    - iIntros (P Q HPQ) "HP". iApply (step_update_mono with "HP"); [done|].
      iIntros "HP!>". by iApply HPQ.
    - iIntros (P Q) "[HP HQ]".
      iDestruct (step_update_comm with "HP HQ") as "HPQ"; [set_solver|].
      by rewrite right_id_L.
  Qed.
  Definition modality_step :=
    Modality _ (modality_step_mixin ).
  Global Instance from_modality_step P :
    FromModal True (modality_step) (|~~> P) (|~~> P) P.
  Proof. by rewrite /FromModal /=. Qed.

  Instance elim_modal_step p P Q :
    ElimModal True p false (|==> P) P (|~~> Q) (|~~> Q).
  Proof.
    destruct p.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]". iDestruct "HP" as "#HP".
      iApply step_update_open. iMod "HP".
      iDestruct ("HPQ" with "HP") as "HQ". iModIntro. iIntros "!>". by iModIntro.
    - rewrite /ElimModal. iIntros (_) "[HP HPQ]". iApply step_update_open.
      iMod "HP". iDestruct ("HPQ" with "HP") as "HQ". by iIntros "!>!>!>".
  Qed.

  Lemma my_lemma P Q :
    (|~~> P) -∗ (P -∗ Q) -∗ |~~> Q.
  Proof. iIntros "HP HPQ". iIntros "!>". by iApply "HPQ". Qed.

  Lemma my_lemma2 P Q :
    (|~~> P) -∗ (|==> P -∗ Q) -∗ |~~> Q.
  Proof. iIntros "HP HPQ". iMod "HPQ". iIntros "!>". by iApply "HPQ". Qed.

End with_Σ.
