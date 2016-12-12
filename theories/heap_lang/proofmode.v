From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Export wp_tactics lifting.
Import uPred.

Ltac wp_strip_later ::= iNext.

Section heap.
Context `{heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (iResUR Σ).

Lemma tac_wp_alloc Δ Δ' E j e v Φ :
  to_val e = Some v →
  IntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦ v)) Δ' = Some Δ'' ∧
    (Δ'' ⊢ Φ (LitV (LitLoc l)))) →
  Δ ⊢ WP Alloc e @ E {{ Φ }}.
Proof.
  intros ?? HΔ. eapply wand_apply; first exact: wp_alloc.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  by rewrite right_id HΔ'.
Qed.

Lemma tac_wp_load Δ Δ' E i l q v Φ :
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  (Δ' ⊢ Φ v) →
  Δ ⊢ WP Load (Lit (LitLoc l)) @ E {{ Φ }}.
Proof.
  intros. eapply wand_apply; first exact: wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_store Δ Δ' Δ'' E i l v e v' Φ :
  to_val e = Some v' →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  (Δ'' ⊢ Φ (LitV LitUnit)) →
  Δ ⊢ WP Store (Lit (LitLoc l)) e @ E {{ Φ }}.
Proof.
  intros. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_fail Δ Δ' E i l q v e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I → v ≠ v1 →
  (Δ' ⊢ Φ (LitV (LitBool false))) →
  Δ ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
Proof.
  intros. eapply wand_apply; first exact: wp_cas_fail.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_suc Δ Δ' Δ'' E i l v e1 v1 e2 v2 Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I → v = v1 →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' = Some Δ'' →
  (Δ'' ⊢ Φ (LitV (LitBool true))) →
  Δ ⊢ WP CAS (Lit (LitLoc l)) e1 e2 @ E {{ Φ }}.
Proof.
  intros; subst. eapply wand_apply; first exact: wp_cas_suc.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
End heap.

Tactic Notation "wp_apply" open_constr(lem) :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    wp_bind_core K; iApply lem; try iNext)
  | _ => fail "wp_apply: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with Alloc _ => wp_bind_core K end)
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    eapply tac_wp_alloc with _ H _;
      [let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_alloc:" e' "not a value"
      |apply _
      |first [intros l | fail 1 "wp_alloc:" l "not fresh"];
        eexists; split;
          [env_cbv; reflexivity || fail "wp_alloc:" H "not fresh"
          |wp_finish]]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  let H := iFresh in wp_alloc l as H.

Tactic Notation "wp_load" :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with Load _ => wp_bind_core K end)
      |fail 1 "wp_load: cannot find 'Load' in" e];
    eapply tac_wp_load;
      [apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
       iAssumptionCore || fail "wp_load: cannot find" l "↦ ?"
      |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with Store _ _ => wp_bind_core K end)
      |fail 1 "wp_store: cannot find 'Store' in" e];
    eapply tac_wp_store;
      [let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_store:" e' "not a value"
      |apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
       iAssumptionCore || fail "wp_store: cannot find" l "↦ ?"
      |env_cbv; reflexivity
      |wp_finish]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_cas_fail" :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with CAS _ _ _ => wp_bind_core K end)
      |fail 1 "wp_cas_fail: cannot find 'CAS' in" e];
    eapply tac_wp_cas_fail;
      [let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_cas_fail:" e' "not a value"
      |let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_cas_fail:" e' "not a value"
      |apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
       iAssumptionCore || fail "wp_cas_fail: cannot find" l "↦ ?"
      |try congruence
      |wp_finish]
  | _ => fail "wp_cas_fail: not a 'wp'"
  end.

Tactic Notation "wp_cas_suc" :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with CAS _ _ _ => wp_bind_core K end)
      |fail 1 "wp_cas_suc: cannot find 'CAS' in" e];
    eapply tac_wp_cas_suc;
      [let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_cas_suc:" e' "not a value"
      |let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_cas_suc:" e' "not a value"
      |apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
       iAssumptionCore || fail "wp_cas_suc: cannot find" l "↦ ?"
      |try congruence
      |env_cbv; reflexivity
      |wp_finish]
  | _ => fail "wp_cas_suc: not a 'wp'"
  end.