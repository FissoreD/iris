From iris.bi Require Export bi telescopes.
From iris.proofmode Require Export base environments classes modality_instances.
From iris.prelude Require Import options.
Import bi.
Import env_notations.

Local Open Scope lazy_bool_scope.

(* Coq versions of the tactics *)
Section tactics.
Context {PROP : bi}.
Implicit Types Γ : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types P Q : PROP.

(** * Starting and stopping the proof mode *)
Lemma tac_start P : envs_entails (Envs Enil Enil 1) P → ⊢ P.
Proof.
  rewrite envs_entails_eq !of_envs_eq /=.
  rewrite intuitionistically_True_emp left_id=><-.
  apply and_intro=> //. apply pure_intro; repeat constructor.
Qed.

Lemma tac_stop Δ P :
  (match env_intuitionistic Δ, env_spatial Δ with
   | Enil, Γs => env_to_prop Γs
   | Γp, Enil => □ env_to_prop_and Γp
   | Γp, Γs => □ env_to_prop_and Γp ∗ env_to_prop Γs
   end ⊢ P) →
  envs_entails Δ P.
Proof.
  rewrite envs_entails_eq !of_envs_eq. intros <-.
  rewrite and_elim_r -env_to_prop_and_sound -env_to_prop_sound.
  destruct (env_intuitionistic Δ), (env_spatial Δ);
    by rewrite /= ?intuitionistically_True_emp ?left_id ?right_id.
Qed.

(** * Basic rules *)
Lemma tac_eval Δ Q Q' :
  (∀ (Q'':=Q'), Q'' ⊢ Q) → (* We introduce [Q''] as a let binding so that
    tactics like `reflexivity` as called by [rewrite //] do not eagerly unify
    it with [Q]. See [test_iEval] in [tests/proofmode]. *)
  envs_entails Δ Q' → envs_entails Δ Q.
Proof. by intros <-. Qed.

Lemma tac_eval_in Δ i p P P' Q :
  envs_lookup i Δ = Some (p, P) →
  (∀ (P'':=P'), P ⊢ P') →
  match envs_simple_replace i p (Esnoc Enil i P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_eq /=. intros ? HP ?.
  rewrite envs_simple_replace_singleton_sound //; simpl.
  by rewrite HP wand_elim_r.
Qed.

Class AffineEnv (Γ : env PROP) := affine_env : Forall Affine Γ.
Global Instance affine_env_nil : AffineEnv Enil.
Proof. constructor. Qed.
Global Instance affine_env_snoc Γ i P :
  Affine P → AffineEnv Γ → AffineEnv (Esnoc Γ i P).
Proof. by constructor. Qed.

(* If the BI is affine, no need to walk on the whole environment. *)
Global Instance affine_env_bi `(BiAffine PROP) Γ : AffineEnv Γ | 0.
Proof. induction Γ; apply _. Qed.

Local Instance affine_env_spatial Δ :
  AffineEnv (env_spatial Δ) → Affine ([∗] env_spatial Δ).
Proof. intros H. induction H; simpl; apply _. Qed.

Lemma tac_emp_intro Δ : AffineEnv (env_spatial Δ) → envs_entails Δ emp.
Proof. intros. by rewrite envs_entails_eq (affine (of_envs Δ)). Qed.

Lemma tac_assumption Δ i p P Q :
  envs_lookup i Δ = Some (p,P) →
  FromAssumption p P Q →
  (let Δ' := envs_delete true i p Δ in
   if env_spatial_is_nil Δ' then TCTrue
   else TCOr (Absorbing Q) (AffineEnv (env_spatial Δ'))) →
  envs_entails Δ Q.
Proof.
  intros ?? H. rewrite envs_entails_eq envs_lookup_sound //.
  simpl in *. destruct (env_spatial_is_nil _) eqn:?.
  - by rewrite (env_spatial_is_nil_intuitionistically _) // sep_elim_l.
  - rewrite from_assumption. destruct H; by rewrite sep_elim_l.
Qed.

Lemma tac_assumption_coq Δ P Q :
  (⊢ P) →
  FromAssumption true P Q →
  (if env_spatial_is_nil Δ then TCTrue
   else TCOr (Absorbing Q) (AffineEnv (env_spatial Δ))) →
  envs_entails Δ Q.
Proof.
  rewrite /FromAssumption /bi_emp_valid /= => HP HPQ H.
  rewrite envs_entails_eq -(left_id emp%I bi_sep (of_envs Δ)).
  rewrite -bi.intuitionistically_emp HP HPQ.
  destruct (env_spatial_is_nil _) eqn:?.
  - by rewrite (env_spatial_is_nil_intuitionistically _) // sep_elim_l.
  - destruct H; by rewrite sep_elim_l.
Qed.

Lemma tac_rename Δ i j p P Q :
  envs_lookup i Δ = Some (p,P) →
  match envs_simple_replace i p (Esnoc Enil j P) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_eq=> ??. rewrite envs_simple_replace_singleton_sound //.
  by rewrite wand_elim_r.
Qed.

Lemma tac_clear Δ i p P Q :
  envs_lookup i Δ = Some (p,P) →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  envs_entails (envs_delete true i p Δ) Q →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=> ?? HQ. rewrite envs_lookup_sound //. rewrite HQ.
  by destruct p; rewrite /= sep_elim_r.
Qed.

(** * False *)
Lemma tac_ex_falso Δ Q : envs_entails Δ False → envs_entails Δ Q.
Proof. by rewrite envs_entails_eq -(False_elim Q). Qed.

Lemma tac_false_destruct Δ i p P Q :
  envs_lookup i Δ = Some (p,P) →
  P = False%I →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ??. subst. rewrite envs_lookup_sound //; simpl.
  by rewrite intuitionistically_if_elim sep_elim_l False_elim.
Qed.

(** * Pure *)
Lemma tac_pure_intro Δ Q φ a :
  FromPure a Q φ →
  (if a then AffineEnv (env_spatial Δ) else TCTrue) →
  φ →
  envs_entails Δ Q.
Proof.
  intros ???. rewrite envs_entails_eq -(from_pure a Q). destruct a; simpl.
  - by rewrite (affine (of_envs Δ)) pure_True // affinely_True_emp affinely_emp.
  - by apply pure_intro.
Qed.

Lemma tac_pure Δ i p P φ Q :
  envs_lookup i Δ = Some (p, P) →
  IntoPure P φ →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  (φ → envs_entails (envs_delete true i p Δ) Q) → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=> ?? HPQ HQ.
  rewrite envs_lookup_sound //; simpl. destruct p; simpl.
  - rewrite (into_pure P) -persistently_and_intuitionistically_sep_l persistently_pure.
    by apply pure_elim_l.
  - destruct HPQ.
    + rewrite -(affine_affinely P) (into_pure P) -persistent_and_affinely_sep_l.
      by apply pure_elim_l.
    + rewrite (into_pure P) -(persistent_absorbingly_affinely ⌜ _ ⌝) absorbingly_sep_lr.
      rewrite -persistent_and_affinely_sep_l. apply pure_elim_l=> ?. by rewrite HQ.
Qed.

Lemma tac_pure_revert Δ φ Q : envs_entails Δ (⌜φ⌝ → Q) → (φ → envs_entails Δ Q).
Proof. rewrite envs_entails_eq. intros HΔ ?. by rewrite HΔ pure_True // left_id. Qed.

(** * Intuitionistic *)
Lemma tac_intuitionistic Δ i p P P' Q :
  envs_lookup i Δ = Some (p, P) →
  IntoPersistent p P P' →
  (if p then TCTrue else TCOr (Affine P) (Absorbing Q)) →
  match envs_replace i p true (Esnoc Enil i P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_replace _ _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_eq=>?? HPQ HQ. rewrite envs_replace_singleton_sound //=.
  destruct p; simpl; rewrite /bi_intuitionistically.
  - by rewrite -(into_persistent true P) /= wand_elim_r.
  - destruct HPQ.
    + rewrite -(affine_affinely P) (_ : P = <pers>?false P)%I //
              (into_persistent _ P) wand_elim_r //.
    + rewrite (_ : P = <pers>?false P)%I // (into_persistent _ P).
      by rewrite -{1}absorbingly_intuitionistically_into_persistently
        absorbingly_sep_l wand_elim_r HQ.
Qed.

Lemma tac_spatial Δ i p P P' Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then FromAffinely P' P else TCEq P' P) →
  match envs_replace i p false (Esnoc Enil i P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Proof.
  intros ? HP. destruct (envs_replace _ _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_eq=> <-. rewrite envs_replace_singleton_sound //; simpl.
  destruct p; simpl; last destruct HP.
  - by rewrite intuitionistically_affinely (from_affinely P' P) wand_elim_r.
  - by rewrite wand_elim_r.
Qed.

(** * Implication and wand *)
Lemma tac_impl_intro Δ i P P' Q R :
  FromImpl R P Q →
  (if env_spatial_is_nil Δ then TCTrue else Persistent P) →
  FromAffinely P' P →
  match envs_app false (Esnoc Enil i P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Proof.
  destruct (envs_app _ _ _) eqn:?; last done.
  rewrite /FromImpl envs_entails_eq => <- ???. destruct (env_spatial_is_nil Δ) eqn:?.
  - rewrite (env_spatial_is_nil_intuitionistically Δ) //; simpl. apply impl_intro_l.
    rewrite envs_app_singleton_sound //; simpl.
    rewrite -(from_affinely P' P) -affinely_and_lr.
    by rewrite persistently_and_intuitionistically_sep_r intuitionistically_elim wand_elim_r.
  - apply impl_intro_l. rewrite envs_app_singleton_sound //; simpl.
    by rewrite -(from_affinely P' P) persistent_and_affinely_sep_l_1 wand_elim_r.
Qed.
Lemma tac_impl_intro_intuitionistic Δ i P P' Q R :
  FromImpl R P Q →
  IntoPersistent false P P' →
  match envs_app true (Esnoc Enil i P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Proof.
  destruct (envs_app _ _ _) eqn:?; last done.
  rewrite /FromImpl envs_entails_eq => <- ??.
  rewrite envs_app_singleton_sound //=. apply impl_intro_l.
  rewrite (_ : P = <pers>?false P)%I // (into_persistent false P).
  by rewrite persistently_and_intuitionistically_sep_l wand_elim_r.
Qed.
Lemma tac_impl_intro_drop Δ P Q R :
  FromImpl R P Q → envs_entails Δ Q → envs_entails Δ R.
Proof.
  rewrite /FromImpl envs_entails_eq => <- ?. apply impl_intro_l. by rewrite and_elim_r.
Qed.

Lemma tac_wand_intro Δ i P Q R :
  FromWand R P Q →
  match envs_app false (Esnoc Enil i P) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Proof.
  destruct (envs_app _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite /FromWand envs_entails_eq => <- HQ.
  rewrite envs_app_sound //; simpl. by rewrite right_id HQ.
Qed.

Lemma tac_wand_intro_intuitionistic Δ i P P' Q R :
  FromWand R P Q →
  IntoPersistent false P P' →
  TCOr (Affine P) (Absorbing Q) →
  match envs_app true (Esnoc Enil i P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ R.
Proof.
  destruct (envs_app _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite /FromWand envs_entails_eq => <- ? HPQ HQ.
  rewrite envs_app_singleton_sound //=. apply wand_intro_l. destruct HPQ.
  - rewrite -(affine_affinely P) (_ : P = <pers>?false P)%I //
            (into_persistent _ P) wand_elim_r //.
  - rewrite (_ : P = <pers>?false P)%I // (into_persistent _ P).
    by rewrite -{1}absorbingly_intuitionistically_into_persistently
      absorbingly_sep_l wand_elim_r HQ.
Qed.
Lemma tac_wand_intro_drop Δ P Q R :
  FromWand R P Q →
  TCOr (Affine P) (Absorbing Q) →
  envs_entails Δ Q →
  envs_entails Δ R.
Proof.
  rewrite envs_entails_eq /FromWand => <- HPQ ->. apply wand_intro_l. by rewrite sep_elim_r.
Qed.

(* This is pretty much [tac_specialize_assert] with [js:=[j]] and [tac_exact],
but it is doing some work to keep the order of hypotheses preserved. *)
Lemma tac_specialize remove_intuitionistic Δ i p j q P1 P2 R Q :
  envs_lookup i Δ = Some (p, P1) →
  let Δ' := envs_delete remove_intuitionistic i p Δ in
  envs_lookup j Δ' = Some (q, R) →
  IntoWand q p R P1 P2 →
  match envs_replace j q (p &&& q) (Esnoc Enil j P2) Δ' with
  | Some Δ'' => envs_entails Δ'' Q
  | None => False
  end → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq /IntoWand. intros ?? HR ?.
  destruct (envs_replace _ _ _ _ _) as [Δ''|] eqn:?; last done.
  rewrite (envs_lookup_sound' _ remove_intuitionistic) //.
  rewrite envs_replace_singleton_sound //. destruct p; simpl in *.
  - rewrite -{1}intuitionistically_idemp -{1}intuitionistically_if_idemp.
    rewrite {1}(intuitionistically_intuitionistically_if q).
    by rewrite HR assoc intuitionistically_if_sep_2 !wand_elim_r.
  - by rewrite HR assoc !wand_elim_r.
Qed.

Lemma tac_specialize_assert Δ j (q am neg : bool) js R P1 P2 P1' Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q false R P1 P2 →
  (if am then AddModal P1' P1 Q else TCEq P1' P1) →
  match
    '(Δ1,Δ2) ← envs_split (if neg is true then Right else Left)
                          js (envs_delete true j q Δ);
    Δ2' ← envs_app (negb am &&& q &&& env_spatial_is_nil Δ1) (Esnoc Enil j P2) Δ2;
    Some (Δ1,Δ2') (* does not preserve position of [j] *)
  with
  | Some (Δ1,Δ2') =>
     (* The constructor [conj] of [∧] still stores the contexts [Δ1] and [Δ2'] *)
     envs_entails Δ1 P1' ∧ envs_entails Δ2' Q
  | None => False
  end → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros ?? Hmod HQ.
  destruct (_ ≫= _) as [[Δ1 Δ2']|] eqn:?; last done.
  destruct HQ as [HP1 HQ].
  destruct (envs_split _ _ _) as [[? Δ2]|] eqn:?; simplify_eq/=;
    destruct (envs_app _ _ _) eqn:?; simplify_eq/=.
  rewrite envs_lookup_sound // envs_split_sound //.
  rewrite (envs_app_singleton_sound Δ2) //; simpl.
  rewrite -intuitionistically_if_idemp (into_wand q false) /=.
  destruct (negb am &&& q &&& env_spatial_is_nil Δ1) eqn:Hp; simpl.
  - move: Hp. rewrite !lazy_andb_true negb_true. intros [[-> ->] ?]; simpl.
    destruct Hmod. rewrite env_spatial_is_nil_intuitionistically // HP1.
    by rewrite assoc intuitionistically_sep_2 wand_elim_l wand_elim_r HQ.
  - rewrite intuitionistically_if_elim HP1. destruct am; last destruct Hmod.
    + by rewrite assoc -(comm _ P1') -assoc wand_trans HQ.
    + by rewrite assoc wand_elim_l wand_elim_r HQ.
Qed.

Lemma tac_unlock_emp Δ Q : envs_entails Δ Q → envs_entails Δ (emp ∗ locked Q).
Proof. rewrite envs_entails_eq=> ->. by rewrite -lock left_id. Qed.
Lemma tac_unlock_True Δ Q : envs_entails Δ Q → envs_entails Δ (True ∗ locked Q).
Proof. rewrite envs_entails_eq=> ->. by rewrite -lock -True_sep_2. Qed.
Lemma tac_unlock Δ Q : envs_entails Δ Q → envs_entails Δ (locked Q).
Proof. by unlock. Qed.

Lemma tac_specialize_frame Δ j (q am : bool) R P1 P2 P1' Q Q' :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q false R P1 P2 →
  (if am then AddModal P1' P1 Q else TCEq P1' P1) →
  envs_entails (envs_delete true j q Δ) (P1' ∗ locked Q') →
  Q' = (P2 -∗ Q)%I →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros ?? Hmod HPQ ->.
  rewrite envs_lookup_sound //. rewrite HPQ -lock.
  rewrite (into_wand q false) /= assoc -(comm _ P1') -assoc wand_trans.
  destruct am; [done|destruct Hmod]. by rewrite wand_elim_r.
Qed.

Lemma tac_specialize_assert_pure Δ j q a R P1 P2 φ Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q true R P1 P2 →
  FromPure a P1 φ →
  φ →
  match envs_simple_replace j q (Esnoc Enil j P2) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:?; last done.
  rewrite envs_entails_eq=> ?????. rewrite envs_simple_replace_singleton_sound //=.
  rewrite -intuitionistically_if_idemp (into_wand q true) /=.
  rewrite -(from_pure a P1) pure_True //.
  rewrite -affinely_affinely_if affinely_True_emp affinely_emp.
  by rewrite intuitionistically_emp left_id wand_elim_r.
Qed.

Lemma tac_specialize_assert_intuitionistic Δ j q P1 P1' P2 R Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q true R P1 P2 →
  Persistent P1 →
  IntoAbsorbingly P1' P1 →
  envs_entails (envs_delete true j q Δ) P1' →
  match envs_simple_replace j q (Esnoc Enil j P2) Δ with
  | Some Δ'' => envs_entails Δ'' Q
  | None => False
  end → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ???? HP1 HQ.
  destruct (envs_simple_replace _ _ _ _) as [Δ''|] eqn:?; last done.
  rewrite -HQ envs_lookup_sound //.
  rewrite -(idemp bi_and (of_envs (envs_delete _ _ _ _))).
  rewrite {2}envs_simple_replace_singleton_sound' //; simpl.
  rewrite {1}HP1 (into_absorbingly P1' P1) (persistent_persistently_2 P1).
  rewrite absorbingly_elim_persistently persistently_and_intuitionistically_sep_l assoc.
  rewrite -intuitionistically_if_idemp -intuitionistically_idemp.
  rewrite (intuitionistically_intuitionistically_if q).
  by rewrite intuitionistically_if_sep_2 (into_wand q true) wand_elim_l wand_elim_r.
Qed.

Lemma tac_specialize_intuitionistic_helper Δ j q P R R' Q :
  envs_lookup j Δ = Some (q,P) →
  (if q then TCTrue else BiAffine PROP) →
  envs_entails Δ (<absorb> R) →
  IntoPersistent false R R' →
  match envs_replace j q true (Esnoc Enil j R') Δ with
  | Some Δ'' => envs_entails Δ'' Q
  | None => False
  end → envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ?? HR ??.
  destruct (envs_replace _ _ _ _ _) as [Δ'|] eqn:?; last done.
  rewrite -(idemp bi_and (of_envs Δ)) {1}HR.
  rewrite envs_replace_singleton_sound //; destruct q; simpl.
  - by rewrite (_ : R = <pers>?false R)%I // (into_persistent _ R)
      absorbingly_elim_persistently sep_elim_r
      persistently_and_intuitionistically_sep_l wand_elim_r.
  - by rewrite (absorbing_absorbingly R) (_ : R = <pers>?false R)%I //
      (into_persistent _ R) sep_elim_r
      persistently_and_intuitionistically_sep_l wand_elim_r.
Qed.

(* A special version of [tac_assumption] that does not do any of the
[FromAssumption] magic. *)
Lemma tac_specialize_intuitionistic_helper_done Δ i q P :
  envs_lookup i Δ = Some (q,P) →
  envs_entails Δ (<absorb> P).
Proof.
  rewrite envs_entails_eq /bi_absorbingly=> /envs_lookup_sound=> ->.
  rewrite intuitionistically_if_elim comm. f_equiv; auto using pure_intro.
Qed.

Lemma tac_revert Δ i Q :
  match envs_lookup_delete true i Δ with
  | Some (p,P,Δ') => envs_entails Δ' ((if p then □ P else P)%I -∗ Q)
  | None => False
  end →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => HQ.
  destruct (envs_lookup_delete _ _ _) as [[[p P] Δ']|] eqn:?; last done.
  rewrite envs_lookup_delete_sound //=.
  rewrite HQ. destruct p; simpl; auto using wand_elim_r.
Qed.

Class IntoIH (φ : Prop) (Δ : envs PROP) (Q : PROP) :=
  into_ih : φ → of_envs Δ ⊢ Q.
Global Instance into_ih_entails Δ Q : IntoIH (envs_entails Δ Q) Δ Q.
Proof. by rewrite envs_entails_eq /IntoIH. Qed.
Global Instance into_ih_forall {A} (φ : A → Prop) Δ Φ :
  (∀ x, IntoIH (φ x) Δ (Φ x)) → IntoIH (∀ x, φ x) Δ (∀ x, Φ x) | 2.
Proof. rewrite /IntoIH=> HΔ ?. apply forall_intro=> x. by rewrite (HΔ x). Qed.
Global Instance into_ih_impl (φ ψ : Prop) Δ Q :
  IntoIH φ Δ Q → IntoIH (ψ → φ) Δ (⌜ψ⌝ → Q) | 1.
Proof. rewrite /IntoIH=> HΔ ?. apply impl_intro_l, pure_elim_l. auto. Qed.

Lemma tac_revert_ih Δ P Q {φ : Prop} (Hφ : φ) :
  IntoIH φ Δ P →
  env_spatial_is_nil Δ = true →
  envs_entails Δ (<pers> P → Q) →
  envs_entails Δ Q.
Proof.
  rewrite /IntoIH envs_entails_eq. intros HP ? HPQ.
  rewrite (env_spatial_is_nil_intuitionistically Δ) //.
  rewrite -(idemp bi_and (□ (of_envs Δ))%I) {1}HP // HPQ.
  rewrite {1}intuitionistically_into_persistently_1 intuitionistically_elim impl_elim_r //.
Qed.

Lemma tac_assert Δ j P Q :
  match envs_app true (Esnoc Enil j (P -∗ P)%I) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end → envs_entails Δ Q.
Proof.
  destruct (envs_app _ _ _) as [Δ'|] eqn:?; last done.
  rewrite envs_entails_eq=> ?. rewrite (envs_app_singleton_sound Δ) //; simpl.
  by rewrite -(entails_wand P) // intuitionistically_emp emp_wand.
Qed.

Definition IntoEmpValid (φ : Type) (P : PROP) := φ → ⊢ P.
(** These lemmas are [Defined] because the guardedness checker must see
through them. See https://gitlab.mpi-sws.org/iris/iris/issues/274. For the
same reason, their bodies use as little automation as possible. *)
Lemma into_emp_valid_here φ P : AsEmpValid φ P → IntoEmpValid φ P.
Proof. by intros [??]. Defined.
Lemma into_emp_valid_impl (φ ψ : Type) P :
  φ → IntoEmpValid ψ P → IntoEmpValid (φ → ψ) P.
Proof. rewrite /IntoEmpValid => Hφ Hi1 Hi2. apply Hi1, Hi2, Hφ. Defined.
Lemma into_emp_valid_forall {A} (φ : A → Type) P x :
  IntoEmpValid (φ x) P → IntoEmpValid (∀ x : A, φ x) P.
Proof. rewrite /IntoEmpValid => Hi1 Hi2. apply Hi1, Hi2. Defined.
Lemma into_emp_valid_tforall {TT : tele} (φ : TT → Prop) P x :
  IntoEmpValid (φ x) P → IntoEmpValid (∀.. x : TT, φ x) P.
Proof. rewrite /IntoEmpValid tforall_forall=> Hi1 Hi2. apply Hi1, Hi2. Defined.
Lemma into_emp_valid_proj φ P : IntoEmpValid φ P → φ → ⊢ P.
Proof. intros HP. apply HP. Defined.

(** When called by the proof mode, the proof of [P] is produced by calling
[into_emp_valid_proj]. That call must be transparent to the guardedness
checker, per https://gitlab.mpi-sws.org/iris/iris/issues/274; hence, it must
be done _outside_ [tac_pose_proof], so the latter can remain opaque. *)
Lemma tac_pose_proof Δ j P Q :
  (⊢ P) →
  match envs_app true (Esnoc Enil j P) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_app _ _ _) as [Δ'|] eqn:?; last done.
  rewrite envs_entails_eq => HP <-. rewrite envs_app_singleton_sound //=.
  by rewrite -HP /= intuitionistically_emp emp_wand.
Qed.

Lemma tac_pose_proof_hyp Δ i j Q :
  match envs_lookup_delete false i Δ with
  | None => False
  | Some (p, P, Δ') =>
    match envs_app p (Esnoc Enil j P) Δ' with
    | None => False
    | Some Δ'' => envs_entails Δ'' Q
    end
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_lookup_delete _ _ _) as [((p&P)&Δ')|] eqn:Hlookup; last done.
  destruct (envs_app _ _ _) as [Δ''|] eqn:?; last done.
  rewrite envs_entails_eq. move: Hlookup. rewrite envs_lookup_delete_Some.
  intros [? ->] <-.
  rewrite envs_lookup_sound' // envs_app_singleton_sound //=.
  by rewrite wand_elim_r.
Qed.

Lemma tac_apply Δ i p R P1 P2 :
  envs_lookup i Δ = Some (p, R) →
  IntoWand p false R P1 P2 →
  envs_entails (envs_delete true i p Δ) P1 → envs_entails Δ P2.
Proof.
  rewrite envs_entails_eq => ?? HP1. rewrite envs_lookup_sound //.
  by rewrite (into_wand p false) /= HP1 wand_elim_l.
Qed.

(** * Conjunction splitting *)
Lemma tac_and_split Δ P Q1 Q2 :
  FromAnd P Q1 Q2 → envs_entails Δ Q1 → envs_entails Δ Q2 → envs_entails Δ P.
Proof. rewrite envs_entails_eq. intros. rewrite -(from_and P). by apply and_intro. Qed.

(** * Separating conjunction splitting *)
Lemma tac_sep_split Δ d js P Q1 Q2 :
  FromSep P Q1 Q2 →
  match envs_split d js Δ with
  | None => False
  | Some (Δ1,Δ2) => envs_entails Δ1 Q1 ∧ envs_entails Δ2 Q2
  end → envs_entails Δ P.
Proof.
  destruct (envs_split _ _ _) as [(Δ1&Δ2)|] eqn:?; last done.
  rewrite envs_entails_eq=>? [HQ1 HQ2].
  rewrite envs_split_sound //. by rewrite HQ1 HQ2.
Qed.

(** * Combining *)
Class FromSeps {PROP : bi} (P : PROP) (Qs : list PROP) :=
  from_seps : [∗] Qs ⊢ P.
Local Arguments FromSeps {_} _%I _%I.
Local Arguments from_seps {_} _%I _%I {_}.

Global Instance from_seps_nil : @FromSeps PROP emp [].
Proof. by rewrite /FromSeps. Qed.
Global Instance from_seps_singleton P : FromSeps P [P] | 1.
Proof. by rewrite /FromSeps /= right_id. Qed.
Global Instance from_seps_cons P P' Q Qs :
  FromSeps P' Qs → FromSep P Q P' → FromSeps P (Q :: Qs) | 2.
Proof. by rewrite /FromSeps /FromSep /= => ->. Qed.

Lemma tac_combine Δ1 Δ2 Δ3 js p Ps j P Q :
  envs_lookup_delete_list false js Δ1 = Some (p, Ps, Δ2) →
  FromSeps P Ps →
  envs_app p (Esnoc Enil j P) Δ2 = Some Δ3 →
  envs_entails Δ3 Q → envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_eq => ??? <-. rewrite envs_lookup_delete_list_sound //.
  rewrite from_seps. rewrite envs_app_singleton_sound //=.
  by rewrite wand_elim_r.
Qed.

(** * Conjunction/separating conjunction elimination *)
Lemma tac_and_destruct Δ i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then IntoAnd true P P1 P2 else IntoSep P P1 P2) →
  match envs_simple_replace i p (Esnoc (Esnoc Enil j1 P1) j2 P2) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_eq. intros. rewrite envs_simple_replace_sound //=. destruct p.
  - by rewrite (into_and _ P) /= right_id -(comm _ P1) wand_elim_r.
  - by rewrite /= (into_sep P) right_id -(comm _ P1) wand_elim_r.
Qed.

(* Using this tactic, one can destruct a (non-separating) conjunction in the
spatial context as long as one of the conjuncts is thrown away. It corresponds
to the principle of "external choice" in linear logic. *)
Lemma tac_and_destruct_choice Δ i p d j P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) →
  (if p then IntoAnd p P P1 P2 : Type else
    TCOr (IntoAnd p P P1 P2) (TCAnd (IntoSep P P1 P2)
      (if d is Left then TCOr (Affine P2) (Absorbing Q)
       else TCOr (Affine P1) (Absorbing Q)))) →
  match envs_simple_replace i p (Esnoc Enil j (if d is Left then P1 else P2)) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end → envs_entails Δ Q.
Proof.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_entails_eq => ? HP HQ.
  rewrite envs_simple_replace_singleton_sound //=. destruct p.
  { rewrite (into_and _ P) HQ. destruct d; simpl.
    - by rewrite and_elim_l wand_elim_r.
    - by rewrite and_elim_r wand_elim_r. }
  destruct HP as [?|[??]].
  { rewrite (into_and _ P) HQ. destruct d; simpl.
    - by rewrite and_elim_l wand_elim_r.
    - by rewrite and_elim_r wand_elim_r. }
  rewrite (into_sep P) HQ. destruct d; simpl.
  - by rewrite (comm _ P1) -assoc wand_elim_r sep_elim_r.
  - by rewrite -assoc wand_elim_r sep_elim_r.
Qed.

(** * Framing *)
Lemma tac_frame_pure Δ (φ : Prop) P Q :
  φ → Frame true ⌜φ⌝ P Q → envs_entails Δ Q → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq => ? Hframe ->. rewrite -Hframe /=.
  rewrite -persistently_and_intuitionistically_sep_l persistently_pure.
  auto using and_intro, pure_intro.
Qed.

Lemma tac_frame Δ i p R P Q :
  envs_lookup i Δ = Some (p, R) →
  Frame p R P Q →
  envs_entails (envs_delete false i p Δ) Q → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq. intros ? Hframe HQ.
  rewrite (envs_lookup_sound' _ false) //. by rewrite -Hframe HQ.
Qed.

(** * Disjunction *)
Lemma tac_or_l Δ P Q1 Q2 :
  FromOr P Q1 Q2 → envs_entails Δ Q1 → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq=> ? ->. rewrite -(from_or P). by apply or_intro_l'.
Qed.
Lemma tac_or_r Δ P Q1 Q2 :
  FromOr P Q1 Q2 → envs_entails Δ Q2 → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq=> ? ->. rewrite -(from_or P). by apply or_intro_r'.
Qed.

Lemma tac_or_destruct Δ i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) → IntoOr P P1 P2 →
  match envs_simple_replace i p (Esnoc Enil j1 P1) Δ,
        envs_simple_replace i p (Esnoc Enil j2 P2) Δ with
  | Some Δ1, Some Δ2 => envs_entails Δ1 Q ∧ envs_entails Δ2 Q
  | _, _ => False
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_simple_replace i p (Esnoc Enil j1 P1)) as [Δ1|] eqn:?; last done.
  destruct (envs_simple_replace i p (Esnoc Enil j2 P2)) as [Δ2|] eqn:?; last done.
  rewrite envs_entails_eq. intros ?? (HP1&HP2). rewrite envs_lookup_sound //.
  rewrite (into_or P) intuitionistically_if_or sep_or_r; apply or_elim.
  - rewrite (envs_simple_replace_singleton_sound' _ Δ1) //.
    by rewrite wand_elim_r.
  - rewrite (envs_simple_replace_singleton_sound' _ Δ2) //.
    by rewrite wand_elim_r.
Qed.

(** * Forall *)
Lemma tac_forall_intro {A} Δ (Φ : A → PROP) Q name :
  FromForall Q Φ name →
  ( (* see [tac_exist_destruct] for an explanation of this let binding *)
   let _ := name in
   ∀ a, envs_entails Δ (Φ a)) →
  envs_entails Δ Q.
Proof. rewrite envs_entails_eq /FromForall=> <-. apply forall_intro. Qed.

Lemma tac_forall_specialize {A} Δ i p P (Φ : A → PROP) Q :
  envs_lookup i Δ = Some (p, P) → IntoForall P Φ →
  (∃ x : A,
      match envs_simple_replace i p (Esnoc Enil i (Φ x)) Δ with
      | None => False
      | Some Δ' => envs_entails Δ' Q
      end) →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq. intros ?? (x&?).
  destruct (envs_simple_replace) as [Δ'|] eqn:?; last done.
  rewrite envs_simple_replace_singleton_sound //; simpl.
  by rewrite (into_forall P) (forall_elim x) wand_elim_r.
Qed.

Lemma tac_forall_revert {A} Δ (Φ : A → PROP) :
  envs_entails Δ (∀ a, Φ a) → ∀ a, envs_entails Δ (Φ a).
Proof. rewrite envs_entails_eq => HΔ a. by rewrite HΔ (forall_elim a). Qed.

(** * Existential *)
Lemma tac_exist {A} Δ P (Φ : A → PROP) :
  FromExist P Φ → (∃ a, envs_entails Δ (Φ a)) → envs_entails Δ P.
Proof.
  rewrite envs_entails_eq => ? [a ?].
  rewrite -(from_exist P). eauto using exist_intro'.
Qed.

Lemma tac_exist_destruct {A} Δ i p j P (Φ : A → PROP) (name: ident_name) Q :
  envs_lookup i Δ = Some (p, P) → IntoExist P Φ name →
  ( (* this let binding makes it easy for the tactic [iExistDestruct] to use
       [name] (from resolving [IntoExist] in an earlier subgoal) within this
       goal *)
    let _ := name in
    ∀ a,
     match envs_simple_replace i p (Esnoc Enil j (Φ a)) Δ with
     | Some Δ' => envs_entails Δ' Q
     | None => False
     end) →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq => ?? HΦ. rewrite envs_lookup_sound //.
  rewrite (into_exist P) intuitionistically_if_exist sep_exist_r.
  apply exist_elim=> a; specialize (HΦ a) as Hmatch.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_simple_replace_singleton_sound' //; simpl. by rewrite wand_elim_r.
Qed.

(** * Modalities *)
Lemma tac_modal_elim Δ i p p' φ P' P Q Q' :
  envs_lookup i Δ = Some (p, P) →
  ElimModal φ p p' P P' Q Q' →
  φ →
  match envs_replace i p p' (Esnoc Enil i P') Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q'
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_replace _ _ _ _ _) as [Δ'|] eqn:?; last done.
  rewrite envs_entails_eq => ??? HΔ. rewrite envs_replace_singleton_sound //=.
  rewrite HΔ. by eapply elim_modal.
Qed.

(** * Accumulate hypotheses *)
Lemma tac_accu Δ P :
  env_to_prop (env_spatial Δ) = P →
  envs_entails Δ P.
Proof.
  rewrite envs_entails_eq=><-.
  rewrite env_to_prop_sound !of_envs_eq and_elim_r sep_elim_r //.
Qed.

(** * Invariants *)
Lemma tac_inv_elim {X : Type} Δ i j φ p Pinv Pin Pout (Pclose : option (X → PROP))
      Q (Q' : X → PROP) :
  envs_lookup i Δ = Some (p, Pinv) →
  ElimInv φ Pinv Pin Pout Pclose Q Q' →
  φ →
  (∀ R,
    match envs_app false (Esnoc Enil j
      (Pin -∗
       (∀ x, Pout x -∗ pm_option_fun Pclose x -∗? Q' x) -∗
       R
      )%I) (envs_delete false i p Δ)
    with Some Δ'' => envs_entails Δ'' R | None => False end) →
  envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq=> ? Hinv ? /(_ Q) Hmatch.
  destruct (envs_app _ _ _) eqn:?; last done.
  rewrite -Hmatch (envs_lookup_sound' _ false) // envs_app_singleton_sound //; simpl.
  apply wand_elim_r', wand_mono; last done. apply wand_intro_r, wand_intro_r.
  rewrite intuitionistically_if_elim -assoc. destruct Pclose; simpl in *.
  - setoid_rewrite wand_curry. auto.
  - setoid_rewrite <-(right_id emp%I _ (Pout _)). auto.
Qed.

(** * Rewriting *)
Lemma tac_rewrite `{!BiInternalEq PROP} Δ i p Pxy d Q :
  envs_lookup i Δ = Some (p, Pxy) →
  ∀ {A : ofe} (x y : A) (Φ : A → PROP),
    IntoInternalEq Pxy x y →
    (Q ⊣⊢ Φ (if d is Left then y else x)) →
    NonExpansive Φ →
    envs_entails Δ (Φ (if d is Left then x else y)) → envs_entails Δ Q.
Proof.
  intros ? A x y ? HPxy -> ?. rewrite envs_entails_eq.
  apply internal_eq_rewrite'; auto. rewrite {1}envs_lookup_sound //.
  rewrite (into_internal_eq Pxy x y) intuitionistically_if_elim sep_elim_l.
  destruct d; auto using internal_eq_sym.
Qed.

Lemma tac_rewrite_in `{!BiInternalEq PROP} Δ i p Pxy j q P d Q :
  envs_lookup i Δ = Some (p, Pxy) →
  envs_lookup j Δ = Some (q, P) →
  ∀ {A : ofe} (x y : A) (Φ : A → PROP),
    IntoInternalEq Pxy x y →
    (P ⊣⊢ Φ (if d is Left then y else x)) →
    NonExpansive Φ →
    match envs_simple_replace j q (Esnoc Enil j (Φ (if d is Left then x else y))) Δ with
    | None => False
    | Some Δ' => envs_entails Δ' Q
    end →
    envs_entails Δ Q.
Proof.
  rewrite envs_entails_eq /IntoInternalEq => ?? A x y Φ HPxy HP ? Hentails.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:?; last done. rewrite -Hentails.
  rewrite -(idemp bi_and (of_envs Δ)) {2}(envs_lookup_sound _ i) //.
  rewrite (envs_simple_replace_singleton_sound _ _ j) //=.
  rewrite HP HPxy (intuitionistically_if_elim _ (_ ≡ _)) sep_elim_l.
  rewrite persistent_and_affinely_sep_r -assoc. apply wand_elim_r'.
  rewrite -persistent_and_affinely_sep_r. apply impl_elim_r'. destruct d.
  - apply (internal_eq_rewrite x y (λ y, □?q Φ y -∗ of_envs Δ')%I). solve_proper.
  - rewrite internal_eq_sym.
    eapply (internal_eq_rewrite y x (λ y, □?q Φ y -∗ of_envs Δ')%I). solve_proper.
Qed.

(** * Löb *)
Lemma tac_löb Δ i Q :
  BiLöb PROP →
  env_spatial_is_nil Δ = true →
  match envs_app true (Esnoc Enil i (▷ Q)%I) Δ with
  | None => False
  | Some Δ' => envs_entails Δ' Q
  end →
  envs_entails Δ Q.
Proof.
  destruct (envs_app _ _ _) as [Δ'|] eqn:?; last done.
  rewrite envs_entails_eq => ?? HQ.
  rewrite (env_spatial_is_nil_intuitionistically Δ) //.
  rewrite envs_app_singleton_sound //; simpl. rewrite HQ.
  apply löb_wand_intuitionistically.
Qed.
End tactics.

(** * Introduction of modalities *)
(** The following _private_ classes are used internally by [tac_modal_intro] /
[iModIntro] to transform the proofmode environments when introducing a modality.

The class [TransformIntuitionisticEnv M C Γin Γout] is used to transform the
intuitionistic environment using a type class [C].

Inputs:
- [Γin] : the original environment.
- [M] : the modality that the environment should be transformed into.
- [C : PROP → PROP → Prop] : a type class that is used to transform the
  individual hypotheses. The first parameter is the input and the second
  parameter is the output.

Outputs:
- [Γout] : the resulting environment. *)
Class TransformIntuitionisticEnv {PROP1 PROP2} (M : modality PROP1 PROP2)
    (C : PROP2 → PROP1 → Prop) (Γin : env PROP2) (Γout : env PROP1) := {
  transform_intuitionistic_env :
    (∀ P Q, C P Q → □ P ⊢ M (□ Q)) →
    (∀ P Q, M P ∧ M Q ⊢ M (P ∧ Q)) →
    □ ([∧] Γin) ⊢ M (□ ([∧] Γout));
  transform_intuitionistic_env_wf : env_wf Γin → env_wf Γout;
  transform_intuitionistic_env_dom i : Γin !! i = None → Γout !! i = None;
}.

(* The class [TransformSpatialEnv M C Γin Γout filtered] is used to transform
the spatial environment using a type class [C].

Inputs:
- [Γin] : the original environment.
- [M] : the modality that the environment should be transformed into.
- [C : PROP → PROP → Prop] : a type class that is used to transform the
  individual hypotheses. The first parameter is the input and the second
  parameter is the output.

Outputs:
- [Γout] : the resulting environment.
- [filtered] : a Boolean indicating if non-affine hypotheses have been cleared. *)
Class TransformSpatialEnv {PROP1 PROP2} (M : modality PROP1 PROP2)
    (C : PROP2 → PROP1 → Prop) (Γin : env PROP2) (Γout : env PROP1)
    (filtered : bool) := {
  transform_spatial_env :
    (∀ P Q, C P Q → P ⊢ M Q) →
    ([∗] Γin) ⊢ M ([∗] Γout) ∗ if filtered then True else emp;
  transform_spatial_env_wf : env_wf Γin → env_wf Γout;
  transform_spatial_env_dom i : Γin !! i = None → Γout !! i = None;
}.

(* The class [IntoModalIntuitionisticEnv M Γin Γout s] is used to transform the
intuitionistic environment with respect to the behavior needed to introduce [M] as
given by [s : modality_intro_spec PROP1 PROP2].

Inputs:
- [Γin] : the original environment.
- [M] : the modality that the environment should be transformed into.
- [s] : the [modality_intro_spec] a specification of the way the hypotheses
  should be transformed.

Outputs:
- [Γout] : the resulting environment. *)
Inductive IntoModalIntuitionisticEnv {PROP2} : ∀ {PROP1} (M : modality PROP1 PROP2)
    (Γin : env PROP2) (Γout : env PROP1), modality_action PROP1 PROP2 → Prop :=
  | MIEnvIsEmpty_intuitionistic {PROP1} (M : modality PROP1 PROP2) :
     IntoModalIntuitionisticEnv M Enil Enil MIEnvIsEmpty
  | MIEnvForall_intuitionistic (M : modality PROP2 PROP2) (C : PROP2 → Prop) Γ :
     TCForall C (env_to_list Γ) →
     IntoModalIntuitionisticEnv M Γ Γ (MIEnvForall C)
  | MIEnvTransform_intuitionistic {PROP1}
       (M : modality PROP1 PROP2) (C : PROP2 → PROP1 → Prop) Γin Γout :
     TransformIntuitionisticEnv M C Γin Γout →
     IntoModalIntuitionisticEnv M Γin Γout (MIEnvTransform C)
  | MIEnvClear_intuitionistic {PROP1 : bi} (M : modality PROP1 PROP2) Γ :
     IntoModalIntuitionisticEnv M Γ Enil MIEnvClear
  | MIEnvId_intuitionistic (M : modality PROP2 PROP2) Γ :
     IntoModalIntuitionisticEnv M Γ Γ MIEnvId.
Existing Class IntoModalIntuitionisticEnv.
Global Existing Instances MIEnvIsEmpty_intuitionistic MIEnvForall_intuitionistic
  MIEnvTransform_intuitionistic MIEnvClear_intuitionistic MIEnvId_intuitionistic.

(* The class [IntoModalSpatialEnv M Γin Γout s] is used to transform the spatial
environment with respect to the behavior needed to introduce [M] as given by
[s : modality_intro_spec PROP1 PROP2].

Inputs:
- [Γin] : the original environment.
- [M] : the modality that the environment should be transformed into.
- [s] : the [modality_intro_spec] a specification of the way the hypotheses
  should be transformed.

Outputs:
- [Γout] : the resulting environment.
- [filtered] : a Boolean indicating if non-affine hypotheses have been cleared. *)
Inductive IntoModalSpatialEnv {PROP2} : ∀ {PROP1} (M : modality PROP1 PROP2)
    (Γin : env PROP2) (Γout : env PROP1), modality_action PROP1 PROP2 → bool → Prop :=
  | MIEnvIsEmpty_spatial {PROP1} (M : modality PROP1 PROP2) :
     IntoModalSpatialEnv M Enil Enil MIEnvIsEmpty false
  | MIEnvForall_spatial (M : modality PROP2 PROP2) (C : PROP2 → Prop) Γ :
     TCForall C (env_to_list Γ) →
     IntoModalSpatialEnv M Γ Γ (MIEnvForall C) false
  | MIEnvTransform_spatial {PROP1}
       (M : modality PROP1 PROP2) (C : PROP2 → PROP1 → Prop) Γin Γout fi :
     TransformSpatialEnv M C Γin Γout fi →
     IntoModalSpatialEnv M Γin Γout (MIEnvTransform C) fi
  | MIEnvClear_spatial {PROP1 : bi} (M : modality PROP1 PROP2) Γ :
     IntoModalSpatialEnv M Γ Enil MIEnvClear false
  | MIEnvId_spatial (M : modality PROP2 PROP2) Γ :
     IntoModalSpatialEnv M Γ Γ MIEnvId false.
Existing Class IntoModalSpatialEnv.
Global Existing Instances MIEnvIsEmpty_spatial MIEnvForall_spatial
  MIEnvTransform_spatial MIEnvClear_spatial MIEnvId_spatial.

Section tac_modal_intro.
  Context {PROP1 PROP2 : bi} (M : modality PROP1 PROP2).

  Global Instance transform_intuitionistic_env_nil C : TransformIntuitionisticEnv M C Enil Enil.
  Proof.
    split; [|eauto using Enil_wf|done]=> /= ??.
    rewrite !intuitionistically_True_emp -modality_emp //.
  Qed.
  Global Instance transform_intuitionistic_env_snoc (C : PROP2 → PROP1 → Prop) Γ Γ' i P Q :
    C P Q →
    TransformIntuitionisticEnv M C Γ Γ' →
    TransformIntuitionisticEnv M C (Esnoc Γ i P) (Esnoc Γ' i Q).
  Proof.
    intros ? [HΓ Hwf Hdom]; split; simpl.
    - intros HC Hand. rewrite intuitionistically_and HC // HΓ //.
      by rewrite Hand -intuitionistically_and.
    - inversion 1; constructor; auto.
    - intros j. destruct (ident_beq _ _); naive_solver.
  Qed.
  Global Instance transform_intuitionistic_env_snoc_not (C : PROP2 → PROP1 → Prop) Γ Γ' i P :
    TransformIntuitionisticEnv M C Γ Γ' →
    TransformIntuitionisticEnv M C (Esnoc Γ i P) Γ' | 100.
  Proof.
    intros [HΓ Hwf Hdom]; split; simpl.
    - intros HC Hand. by rewrite and_elim_r HΓ.
    - inversion 1; auto.
    - intros j. destruct (ident_beq _ _); naive_solver.
  Qed.

  Global Instance transform_spatial_env_nil C :
    TransformSpatialEnv M C Enil Enil false.
  Proof.
    split; [|eauto using Enil_wf|done]=> /= ?. by rewrite right_id -modality_emp.
  Qed.
  Global Instance transform_spatial_env_snoc (C : PROP2 → PROP1 → Prop) Γ Γ' i P Q fi :
    C P Q →
    TransformSpatialEnv M C Γ Γ' fi →
    TransformSpatialEnv M C (Esnoc Γ i P) (Esnoc Γ' i Q) fi.
  Proof.
    intros ? [HΓ Hwf Hdom]; split; simpl.
    - intros HC. by rewrite {1}(HC P) // HΓ // assoc modality_sep.
    - inversion 1; constructor; auto.
    - intros j. destruct (ident_beq _ _); naive_solver.
  Qed.

  Global Instance transform_spatial_env_snoc_not
      (C : PROP2 → PROP1 → Prop) Γ Γ' i P fi fi' :
    TransformSpatialEnv M C Γ Γ' fi →
    TCIf (TCEq fi false)
      (TCIf (Affine P) (TCEq fi' false) (TCEq fi' true))
      (TCEq fi' true) →
    TransformSpatialEnv M C (Esnoc Γ i P) Γ' fi' | 100.
  Proof.
    intros [HΓ Hwf Hdom] Hif; split; simpl.
    - intros ?. rewrite HΓ //. destruct Hif as [-> [? ->| ->]| ->].
      + by rewrite (affine P) left_id.
      + by rewrite right_id comm (True_intro P).
      + by rewrite comm -assoc (True_intro (_ ∗ P)).
    - inversion 1; auto.
    - intros j. destruct (ident_beq _ _); naive_solver.
  Qed.

  (** The actual introduction tactic *)
  Lemma tac_modal_intro {A} φ (sel : A) Γp Γs n Γp' Γs' Q Q' fi :
    FromModal φ M sel Q' Q →
    IntoModalIntuitionisticEnv M Γp Γp' (modality_intuitionistic_action M) →
    IntoModalSpatialEnv M Γs Γs' (modality_spatial_action M) fi →
    (if fi then Absorbing Q' else TCTrue) →
    φ →
    envs_entails (Envs Γp' Γs' n) Q → envs_entails (Envs Γp Γs n) Q'.
  Proof.
    rewrite envs_entails_eq /FromModal !of_envs_eq => HQ' HΓp HΓs ? Hφ HQ.
    apply pure_elim_l=> -[???]. assert (envs_wf (Envs Γp' Γs' n)) as Hwf.
    { split; simpl in *.
      - destruct HΓp as [| |????? []| |]; eauto using Enil_wf.
      - destruct HΓs as [| |?????? []| |]; eauto using Enil_wf.
      - assert (∀ i, Γp !! i = None → Γp' !! i = None).
        { destruct HΓp as [| |????? []| |]; eauto. }
        assert (∀ i, Γs !! i = None → Γs' !! i = None).
        { destruct HΓs as [| |?????? []| |]; eauto. }
        naive_solver. }
    assert (□ [∧] Γp ⊢ M (□ [∧] Γp'))%I as HMp.
    { remember (modality_intuitionistic_action M).
      destruct HΓp as [? M|M C Γp ?%TCForall_Forall|? M C Γp Γp' []|? M Γp|M Γp]; simpl.
      - rewrite {1}intuitionistically_elim_emp (modality_emp M)
          intuitionistically_True_emp //.
      - eauto using modality_intuitionistic_forall_big_and.
      - eauto using modality_intuitionistic_transform,
          modality_and_transform.
      - by rewrite {1}intuitionistically_elim_emp (modality_emp M)
          intuitionistically_True_emp.
      - eauto using modality_intuitionistic_id. }
    move: HQ'; rewrite -HQ pure_True // left_id HMp=> HQ' {HQ Hwf HMp}.
    remember (modality_spatial_action M).
    destruct HΓs as [? M|M C Γs ?%TCForall_Forall|? M C Γs Γs' fi []|? M Γs|M Γs]; simpl.
    - by rewrite -HQ' //= !right_id.
    - rewrite -HQ' // {1}(modality_spatial_forall_big_sep _ _ Γs) //.
      by rewrite modality_sep.
    - destruct fi.
      + rewrite -(absorbing Q') /bi_absorbingly -HQ' // (comm _ True%I).
        rewrite -modality_sep -assoc. apply sep_mono_r.
        eauto using modality_spatial_transform.
      + rewrite -HQ' // -modality_sep. apply sep_mono_r.
        rewrite -(right_id emp%I bi_sep (M _)).
        eauto using modality_spatial_transform.
    - rewrite -HQ' //= right_id comm -{2}(modality_spatial_clear M) //.
      by rewrite (True_intro ([∗] Γs)).
    - rewrite -HQ' // {1}(modality_spatial_id M ([∗] Γs)) //.
      by rewrite -modality_sep.
  Qed.
End tac_modal_intro.

(** The class [MaybeIntoLaterNEnvs] is used by tactics that need to introduce
laters, e.g., the symbolic execution tactics. *)
Class MaybeIntoLaterNEnvs {PROP : bi} (n : nat) (Δ1 Δ2 : envs PROP) := {
  into_later_intuitionistic :
    TransformIntuitionisticEnv (modality_laterN n) (MaybeIntoLaterN false n)
      (env_intuitionistic Δ1) (env_intuitionistic Δ2);
  into_later_spatial :
    TransformSpatialEnv (modality_laterN n)
      (MaybeIntoLaterN false n) (env_spatial Δ1) (env_spatial Δ2) false
}.

Global Instance into_laterN_envs {PROP : bi} n (Γp1 Γp2 Γs1 Γs2 : env PROP) m :
  TransformIntuitionisticEnv (modality_laterN n) (MaybeIntoLaterN false n) Γp1 Γp2 →
  TransformSpatialEnv (modality_laterN n) (MaybeIntoLaterN false n) Γs1 Γs2 false →
  MaybeIntoLaterNEnvs n (Envs Γp1 Γs1 m) (Envs Γp2 Γs2 m).
Proof. by split. Qed.

Lemma into_laterN_env_sound {PROP : bi} n (Δ1 Δ2 : envs PROP) :
  MaybeIntoLaterNEnvs n Δ1 Δ2 → of_envs Δ1 ⊢ ▷^n (of_envs Δ2).
Proof.
  intros [[Hp ??] [Hs ??]]; rewrite !of_envs_eq /= !laterN_and !laterN_sep.
  rewrite -{1}laterN_intro. apply and_mono, sep_mono.
  - apply pure_mono; destruct 1; constructor; naive_solver.
  - apply Hp; rewrite /= /MaybeIntoLaterN.
    + intros P Q ->. by rewrite laterN_intuitionistically_2.
    + intros P Q. by rewrite laterN_and.
  - by rewrite Hs //= right_id.
Qed.
