From iris.base_logic Require Export base_logic.
From iris.base_logic Require Import big_op tactics.
From iris.proofmode Require Export environments classes.
From stdpp Require Import stringmap hlist.
Set Default Proof Using "Type".
Import uPred.
Import env_notations.

Local Notation "b1 && b2" := (if b1 then b2 else false) : bool_scope.

Record envs (M : ucmraT) :=
  Envs { env_persistent : env (uPred M); env_spatial : env (uPred M) }.
Add Printing Constructor envs.
Arguments Envs {_} _ _.
Arguments env_persistent {_} _.
Arguments env_spatial {_} _.

Record envs_wf {M} (Δ : envs M) := {
  env_persistent_valid : env_wf (env_persistent Δ);
  env_spatial_valid : env_wf (env_spatial Δ);
  envs_disjoint i : env_persistent Δ !! i = None ∨ env_spatial Δ !! i = None
}.

Coercion of_envs {M} (Δ : envs M) : uPred M :=
  (⌜envs_wf Δ⌝ ∗ □ [∗] env_persistent Δ ∗ [∗] env_spatial Δ)%I.
Instance: Params (@of_envs) 1.

Record envs_Forall2 {M} (R : relation (uPred M)) (Δ1 Δ2 : envs M) : Prop := {
  env_persistent_Forall2 : env_Forall2 R (env_persistent Δ1) (env_persistent Δ2);
  env_spatial_Forall2 : env_Forall2 R (env_spatial Δ1) (env_spatial Δ2)
}.

Definition envs_dom {M} (Δ : envs M) : list string :=
  env_dom (env_persistent Δ) ++ env_dom (env_spatial Δ).

Definition envs_lookup {M} (i : string) (Δ : envs M) : option (bool * uPred M) :=
  let (Γp,Γs) := Δ in
  match env_lookup i Γp with
  | Some P => Some (true, P) | None => P ← env_lookup i Γs; Some (false, P)
  end.

Definition envs_delete {M} (i : string) (p : bool) (Δ : envs M) : envs M :=
  let (Γp,Γs) := Δ in
  match p with
  | true => Envs (env_delete i Γp) Γs | false => Envs Γp (env_delete i Γs)
  end.

Definition envs_lookup_delete {M} (i : string)
    (Δ : envs M) : option (bool * uPred M * envs M) :=
  let (Γp,Γs) := Δ in
  match env_lookup_delete i Γp with
  | Some (P,Γp') => Some (true, P, Envs Γp' Γs)
  | None => '(P,Γs') ← env_lookup_delete i Γs; Some (false, P, Envs Γp Γs')
  end.

Fixpoint envs_lookup_delete_list {M} (js : list string) (remove_persistent : bool)
    (Δ : envs M) : option (bool * list (uPred M) * envs M) :=
  match js with
  | [] => Some (true, [], Δ)
  | j :: js =>
     '(p,P,Δ') ← envs_lookup_delete j Δ;
     let Δ' := if p then (if remove_persistent then Δ' else Δ) else Δ' in
     '(q,Hs,Δ'') ← envs_lookup_delete_list js remove_persistent Δ';
     Some (p && q, P :: Hs, Δ'')
  end.

Definition envs_snoc {M} (Δ : envs M)
    (p : bool) (j : string) (P : uPred M) : envs M :=
  let (Γp,Γs) := Δ in
  if p then Envs (Esnoc Γp j P) Γs else Envs Γp (Esnoc Γs j P).

Definition envs_app {M} (p : bool)
    (Γ : env (uPred M)) (Δ : envs M) : option (envs M) :=
  let (Γp,Γs) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_app Γ Γp; Some (Envs Γp' Γs)
  | false => _ ← env_app Γ Γp; Γs' ← env_app Γ Γs; Some (Envs Γp Γs')
  end.

Definition envs_simple_replace {M} (i : string) (p : bool) (Γ : env (uPred M))
    (Δ : envs M) : option (envs M) :=
  let (Γp,Γs) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_replace i Γ Γp; Some (Envs Γp' Γs)
  | false => _ ← env_app Γ Γp; Γs' ← env_replace i Γ Γs; Some (Envs Γp Γs')
  end.

Definition envs_replace {M} (i : string) (p q : bool) (Γ : env (uPred M))
    (Δ : envs M) : option (envs M) :=
  if eqb p q then envs_simple_replace i p Γ Δ
  else envs_app q Γ (envs_delete i p Δ).

Definition env_spatial_is_nil {M} (Δ : envs M) :=
  if env_spatial Δ is Enil then true else false.

Definition envs_clear_spatial {M} (Δ : envs M) : envs M :=
  Envs (env_persistent Δ) Enil.

Definition envs_clear_persistent {M} (Δ : envs M) : envs M :=
  Envs Enil (env_spatial Δ).

Fixpoint envs_split_go {M}
    (js : list string) (Δ1 Δ2 : envs M) : option (envs M * envs M) :=
  match js with
  | [] => Some (Δ1, Δ2)
  | j :: js =>
     '(p,P,Δ1') ← envs_lookup_delete j Δ1;
     if p then envs_split_go js Δ1 Δ2 else
     envs_split_go js Δ1' (envs_snoc Δ2 false j P)
  end.
(* if [lr = true] then [result = (remaining hyps, hyps named js)] and
   if [lr = false] then [result = (hyps named js, remaining hyps)] *)
Definition envs_split {M} (lr : bool)
    (js : list string) (Δ : envs M) : option (envs M * envs M) :=
  '(Δ1,Δ2) ← envs_split_go js Δ (envs_clear_spatial Δ);
  if lr then Some (Δ1,Δ2) else Some (Δ2,Δ1).

(* Coq versions of the tactics *)
Section tactics.
Context {M : ucmraT}.
Implicit Types Γ : env (uPred M).
Implicit Types Δ : envs M.
Implicit Types P Q : uPred M.

Lemma of_envs_def Δ :
  of_envs Δ = (⌜envs_wf Δ⌝ ∗ □ [∗] env_persistent Δ ∗ [∗] env_spatial Δ)%I.
Proof. done. Qed.

Lemma envs_lookup_delete_Some Δ Δ' i p P :
  envs_lookup_delete i Δ = Some (p,P,Δ')
  ↔ envs_lookup i Δ = Some (p,P) ∧ Δ' = envs_delete i p Δ.
Proof.
  rewrite /envs_lookup /envs_delete /envs_lookup_delete.
  destruct Δ as [Γp Γs]; rewrite /= !env_lookup_delete_correct.
  destruct (Γp !! i), (Γs !! i); naive_solver.
Qed.

Lemma envs_lookup_sound Δ i p P :
  envs_lookup i Δ = Some (p,P) → Δ ⊢ □?p P ∗ envs_delete i p Δ.
Proof.
  rewrite /envs_lookup /envs_delete /of_envs=>?; apply pure_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite (env_lookup_perm Γp) //= always_sep.
    ecancel [□ [∗] _; □ P; [∗] Γs]%I; apply pure_intro.
    destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite (env_lookup_perm Γs) //=.
    ecancel [□ [∗] _; P; [∗] (env_delete _ _)]%I; apply pure_intro.
    destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh.
Qed.
Lemma envs_lookup_sound' Δ i p P :
  envs_lookup i Δ = Some (p,P) → Δ ⊢ P ∗ envs_delete i p Δ.
Proof. intros. rewrite envs_lookup_sound //. by rewrite always_if_elim. Qed.
Lemma envs_lookup_persistent_sound Δ i P :
  envs_lookup i Δ = Some (true,P) → Δ ⊢ □ P ∗ Δ.
Proof.
  intros. apply (always_entails_l _ _). by rewrite envs_lookup_sound // sep_elim_l.
Qed.

Lemma envs_lookup_split Δ i p P :
  envs_lookup i Δ = Some (p,P) → Δ ⊢ □?p P ∗ (□?p P -∗ Δ).
Proof.
  rewrite /envs_lookup /of_envs=>?; apply pure_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite (env_lookup_perm Γp) //= always_sep.
    rewrite pure_True // left_id.
    cancel [□ P]%I. apply wand_intro_l. solve_sep_entails.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite (env_lookup_perm Γs) //=. rewrite pure_True // left_id.
    cancel [P]. apply wand_intro_l. solve_sep_entails.
Qed.

Lemma envs_lookup_delete_sound Δ Δ' i p P :
  envs_lookup_delete i Δ = Some (p,P,Δ') → Δ ⊢ □?p P ∗ Δ'.
Proof. intros [? ->]%envs_lookup_delete_Some. by apply envs_lookup_sound. Qed.
Lemma envs_lookup_delete_sound' Δ Δ' i p P :
  envs_lookup_delete i Δ = Some (p,P,Δ') → Δ ⊢ P ∗ Δ'.
Proof. intros [? ->]%envs_lookup_delete_Some. by apply envs_lookup_sound'. Qed.

Lemma envs_lookup_delete_list_sound Δ Δ' js rp p Ps :
  envs_lookup_delete_list js rp Δ = Some (p, Ps,Δ') → Δ ⊢ □?p [∗] Ps ∗ Δ'.
Proof.
  revert Δ Δ' p Ps. induction js as [|j js IH]=> Δ Δ'' p Ps ?; simplify_eq/=.
  { by rewrite always_pure left_id. }
  destruct (envs_lookup_delete j Δ) as [[[q1 P] Δ']|] eqn:Hj; simplify_eq/=.
  apply envs_lookup_delete_Some in Hj as [Hj ->].
  destruct (envs_lookup_delete_list js rp _) as [[[q2 Ps'] ?]|] eqn:?; simplify_eq/=.
  rewrite always_if_sep -assoc. destruct q1; simpl.
  - destruct rp.
    + rewrite envs_lookup_sound //; simpl. by rewrite IH // (always_elim_if q2).
    + rewrite envs_lookup_persistent_sound //. by rewrite IH // (always_elim_if q2).
  - rewrite envs_lookup_sound // IH //; simpl. by rewrite always_if_elim.
Qed.

Lemma envs_lookup_snoc Δ i p P :
  envs_lookup i Δ = None → envs_lookup i (envs_snoc Δ p i P) = Some (p, P).
Proof.
  rewrite /envs_lookup /envs_snoc=> ?.
  destruct Δ as [Γp Γs], p, (Γp !! i); simplify_eq; by rewrite env_lookup_snoc.
Qed.
Lemma envs_lookup_snoc_ne Δ i j p P :
  i ≠ j → envs_lookup i (envs_snoc Δ p j P) = envs_lookup i Δ.
Proof.
  rewrite /envs_lookup /envs_snoc=> ?.
  destruct Δ as [Γp Γs], p; simplify_eq; by rewrite env_lookup_snoc_ne.
Qed.

Lemma envs_snoc_sound Δ p i P :
  envs_lookup i Δ = None → Δ ⊢ □?p P -∗ envs_snoc Δ p i P.
Proof.
  rewrite /envs_lookup /envs_snoc /of_envs=> ?; apply pure_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?, (Γs !! i) eqn:?; simplify_eq/=.
  apply wand_intro_l; destruct p; simpl.
  - apply sep_intro_True_l; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using Esnoc_wf.
      intros j; destruct (strings.string_beq_reflect j i); naive_solver.
    + by rewrite always_sep assoc.
  - apply sep_intro_True_l; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using Esnoc_wf.
      intros j; destruct (strings.string_beq_reflect j i); naive_solver.
    + solve_sep_entails.
Qed.

Lemma envs_app_sound Δ Δ' p Γ : envs_app p Γ Δ = Some Δ' → Δ ⊢ □?p [∗] Γ -∗ Δ'.
Proof.
  rewrite /of_envs /envs_app=> ?; apply pure_elim_sep_l=> Hwf.
  destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_app Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γp') //.
      rewrite big_opL_app always_sep. solve_sep_entails.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_app Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γs') // big_opL_app. solve_sep_entails.
Qed.

Lemma envs_simple_replace_sound' Δ Δ' i p Γ :
  envs_simple_replace i p Γ Δ = Some Δ' →
  envs_delete i p Δ ⊢ □?p [∗] Γ -∗ Δ'.
Proof.
  rewrite /envs_simple_replace /envs_delete /of_envs=> ?.
  apply pure_elim_sep_l=> Hwf. destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_replace i Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γp') //.
      rewrite big_opL_app always_sep. solve_sep_entails.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_replace i Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, sep_intro_True_l; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γs') // big_opL_app. solve_sep_entails.
Qed.

Lemma envs_simple_replace_sound Δ Δ' i p P Γ :
  envs_lookup i Δ = Some (p,P) → envs_simple_replace i p Γ Δ = Some Δ' →
  Δ ⊢ □?p P ∗ (□?p [∗] Γ -∗ Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_simple_replace_sound'//. Qed.

Lemma envs_replace_sound' Δ Δ' i p q Γ :
  envs_replace i p q Γ Δ = Some Δ' → envs_delete i p Δ ⊢ □?q [∗] Γ -∗ Δ'.
Proof.
  rewrite /envs_replace; destruct (eqb _ _) eqn:Hpq.
  - apply eqb_prop in Hpq as ->. apply envs_simple_replace_sound'.
  - apply envs_app_sound.
Qed.

Lemma envs_replace_sound Δ Δ' i p q P Γ :
  envs_lookup i Δ = Some (p,P) → envs_replace i p q Γ Δ = Some Δ' →
  Δ ⊢ □?p P ∗ (□?q [∗] Γ -∗ Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_replace_sound'//. Qed.

Lemma envs_lookup_envs_clear_spatial Δ j :
  envs_lookup j (envs_clear_spatial Δ)
  = '(p,P) ← envs_lookup j Δ; if p then Some (p,P) else None.
Proof.
  rewrite /envs_lookup /envs_clear_spatial.
  destruct Δ as [Γp Γs]; simpl; destruct (Γp !! j) eqn:?; simplify_eq/=; auto.
  by destruct (Γs !! j).
Qed.

Lemma envs_clear_spatial_sound Δ : Δ ⊢ envs_clear_spatial Δ ∗ [∗] env_spatial Δ.
Proof.
  rewrite /of_envs /envs_clear_spatial /=; apply pure_elim_sep_l=> Hwf.
  rewrite right_id -assoc; apply sep_intro_True_l; [apply pure_intro|done].
  destruct Hwf; constructor; simpl; auto using Enil_wf.
Qed.

Lemma env_spatial_is_nil_persistent Δ :
  env_spatial_is_nil Δ = true → PersistentP Δ.
Proof. intros; destruct Δ as [? []]; simplify_eq/=; apply _. Qed.
Hint Immediate env_spatial_is_nil_persistent : typeclass_instances.

Lemma envs_lookup_envs_delete Δ i p P :
  envs_wf Δ →
  envs_lookup i Δ = Some (p,P) → envs_lookup i (envs_delete i p Δ) = None.
Proof.
  rewrite /envs_lookup /envs_delete=> -[?? Hdisj] Hlookup.
  destruct Δ as [Γp Γs], p; simplify_eq/=.
  - rewrite env_lookup_env_delete //. revert Hlookup.
    destruct (Hdisj i) as [->| ->]; [|done]. by destruct (Γs !! _).
  - rewrite env_lookup_env_delete //. by destruct (Γp !! _).
Qed.
Lemma envs_lookup_envs_delete_ne Δ i j p :
  i ≠ j → envs_lookup i (envs_delete j p Δ) = envs_lookup i Δ.
Proof.
  rewrite /envs_lookup /envs_delete=> ?. destruct Δ as [Γp Γs],p; simplify_eq/=.
  - by rewrite env_lookup_env_delete_ne.
  - destruct (Γp !! i); simplify_eq/=; by rewrite ?env_lookup_env_delete_ne.
Qed.

Lemma envs_split_go_sound js Δ1 Δ2 Δ1' Δ2' :
  (∀ j P, envs_lookup j Δ1 = Some (false, P) → envs_lookup j Δ2 = None) →
  envs_split_go js Δ1 Δ2 = Some (Δ1',Δ2') → Δ1 ∗ Δ2 ⊢ Δ1' ∗ Δ2'.
Proof.
  revert Δ1 Δ2 Δ1' Δ2'.
  induction js as [|j js IH]=> Δ1 Δ2 Δ1' Δ2' Hlookup HΔ; simplify_eq/=; [done|].
  apply pure_elim with (envs_wf Δ1); [unfold of_envs; solve_sep_entails|]=> Hwf.
  destruct (envs_lookup_delete j Δ1)
    as [[[[] P] Δ1'']|] eqn:Hdel; simplify_eq; auto.
  apply envs_lookup_delete_Some in Hdel as [??]; subst.
  rewrite envs_lookup_sound //; rewrite /= (comm _ P) -assoc.
  rewrite -(IH _ _ _ _ _ HΔ); last first.
  { intros j' P'; destruct (decide (j = j')) as [->|].
    - by rewrite (envs_lookup_envs_delete _ _ _ P).
    - rewrite envs_lookup_envs_delete_ne // envs_lookup_snoc_ne //. eauto. }
  rewrite (envs_snoc_sound Δ2 false j P) /= ?wand_elim_r; eauto.
Qed.
Lemma envs_split_sound Δ lr js Δ1 Δ2 :
  envs_split lr js Δ = Some (Δ1,Δ2) → Δ ⊢ Δ1 ∗ Δ2.
Proof.
  rewrite /envs_split=> ?. rewrite -(idemp uPred_and Δ).
  rewrite {2}envs_clear_spatial_sound sep_elim_l always_and_sep_r.
  destruct (envs_split_go _ _) as [[Δ1' Δ2']|] eqn:HΔ; [|done].
  apply envs_split_go_sound in HΔ as ->; last first.
  { intros j P. by rewrite envs_lookup_envs_clear_spatial=> ->. }
  destruct lr; simplify_eq; solve_sep_entails.
Qed.

Global Instance envs_Forall2_refl (R : relation (uPred M)) :
  Reflexive R → Reflexive (envs_Forall2 R).
Proof. by constructor. Qed.
Global Instance envs_Forall2_sym (R : relation (uPred M)) :
  Symmetric R → Symmetric (envs_Forall2 R).
Proof. intros ??? [??]; by constructor. Qed.
Global Instance envs_Forall2_trans (R : relation (uPred M)) :
  Transitive R → Transitive (envs_Forall2 R).
Proof. intros ??? [??] [??] [??]; constructor; etrans; eauto. Qed.
Global Instance envs_Forall2_antisymm (R R' : relation (uPred M)) :
  AntiSymm R R' → AntiSymm (envs_Forall2 R) (envs_Forall2 R').
Proof. intros ??? [??] [??]; constructor; by eapply (anti_symm _). Qed.
Lemma envs_Forall2_impl (R R' : relation (uPred M)) Δ1 Δ2 :
  envs_Forall2 R Δ1 Δ2 → (∀ P Q, R P Q → R' P Q) → envs_Forall2 R' Δ1 Δ2.
Proof. intros [??] ?; constructor; eauto using env_Forall2_impl. Qed.

Global Instance of_envs_mono : Proper (envs_Forall2 (⊢) ==> (⊢)) (@of_envs M).
Proof.
  intros [Γp1 Γs1] [Γp2 Γs2] [Hp Hs]; unfold of_envs; simpl in *.
  apply pure_elim_sep_l=>Hwf. apply sep_intro_True_l.
  - destruct Hwf; apply pure_intro; constructor;
      naive_solver eauto using env_Forall2_wf, env_Forall2_fresh.
  - by repeat f_equiv.
Qed.
Global Instance of_envs_proper : Proper (envs_Forall2 (⊣⊢) ==> (⊣⊢)) (@of_envs M).
Proof.
  intros Δ1 Δ2 HΔ; apply (anti_symm (⊢)); apply of_envs_mono;
    eapply (envs_Forall2_impl (⊣⊢)); [| |symmetry|]; eauto using equiv_entails.
Qed.
Global Instance Envs_mono (R : relation (uPred M)) :
  Proper (env_Forall2 R ==> env_Forall2 R ==> envs_Forall2 R) (@Envs M).
Proof. by constructor. Qed.

(** * Adequacy *)
Lemma tac_adequate P : (Envs Enil Enil ⊢ P) → P.
Proof.
  intros <-. rewrite /of_envs /= always_pure !right_id.
  apply pure_intro; repeat constructor.
Qed.

(** * Basic rules *)
Lemma tac_assumption Δ i p P Q :
  envs_lookup i Δ = Some (p,P) → FromAssumption p P Q → Δ ⊢ Q.
Proof. intros. by rewrite envs_lookup_sound // sep_elim_l. Qed.

Lemma tac_rename Δ Δ' i j p P Q :
  envs_lookup i Δ = Some (p,P) →
  envs_simple_replace i p (Esnoc Enil j P) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //.
  destruct p; simpl; by rewrite right_id wand_elim_r.
Qed.
Lemma tac_clear Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof. intros. by rewrite envs_lookup_delete_sound // sep_elim_r. Qed.

(** * False *)
Lemma tac_ex_falso Δ Q : (Δ ⊢ False) → Δ ⊢ Q.
Proof. by rewrite -(False_elim Q). Qed.

(** * Pure *)
Lemma tac_pure_intro Δ Q (φ : Prop) : FromPure Q φ → φ → Δ ⊢ Q.
Proof. intros ??. rewrite -(from_pure Q). by apply pure_intro. Qed.

Lemma tac_pure Δ Δ' i p P φ Q :
  envs_lookup_delete i Δ = Some (p, P, Δ') → IntoPure P φ →
  (φ → Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ?? HQ. rewrite envs_lookup_delete_sound' //; simpl.
  rewrite (into_pure P); by apply pure_elim_sep_l.
Qed.

Lemma tac_pure_revert Δ φ Q : (Δ ⊢ ⌜φ⌝ → Q) → (φ → Δ ⊢ Q).
Proof. intros HΔ ?. by rewrite HΔ pure_True // left_id. Qed.

(** * Later *)
Class IntoLaterNEnv (n : nat) (Γ1 Γ2 : env (uPred M)) :=
  into_laterN_env : env_Forall2 (IntoLaterN n) Γ1 Γ2.
Class IntoLaterNEnvs (n : nat) (Δ1 Δ2 : envs M) := {
  into_later_persistent: IntoLaterNEnv n (env_persistent Δ1) (env_persistent Δ2);
  into_later_spatial: IntoLaterNEnv n (env_spatial Δ1) (env_spatial Δ2)
}.

Global Instance into_laterN_env_nil n : IntoLaterNEnv n Enil Enil.
Proof. constructor. Qed.
Global Instance into_laterN_env_snoc n Γ1 Γ2 i P Q :
  IntoLaterNEnv n Γ1 Γ2 → IntoLaterN n P Q →
  IntoLaterNEnv n (Esnoc Γ1 i P) (Esnoc Γ2 i Q).
Proof. by constructor. Qed.

Global Instance into_laterN_envs n Γp1 Γp2 Γs1 Γs2 :
  IntoLaterNEnv n Γp1 Γp2 → IntoLaterNEnv n Γs1 Γs2 →
  IntoLaterNEnvs n (Envs Γp1 Γs1) (Envs Γp2 Γs2).
Proof. by split. Qed.

Lemma into_laterN_env_sound n Δ1 Δ2 : IntoLaterNEnvs n Δ1 Δ2 → Δ1 ⊢ ▷^n Δ2.
Proof.
  intros [Hp Hs]; rewrite /of_envs /= !laterN_sep -always_laterN.
  repeat apply sep_mono; try apply always_mono.
  - rewrite -laterN_intro; apply pure_mono; destruct 1; constructor;
      naive_solver eauto using env_Forall2_wf, env_Forall2_fresh.
  - induction Hp; rewrite /= ?laterN_sep. apply laterN_intro. by apply sep_mono.
  - induction Hs; rewrite /= ?laterN_sep. apply laterN_intro. by apply sep_mono.
Qed.

Lemma tac_next Δ Δ' n Q Q' :
  FromLaterN n Q Q' → IntoLaterNEnvs n Δ Δ' → (Δ' ⊢ Q') → Δ ⊢ Q.
Proof. intros ?? HQ. by rewrite -(from_laterN n Q) into_laterN_env_sound HQ. Qed.

Lemma tac_löb Δ Δ' i Q :
  env_spatial_is_nil Δ = true →
  envs_app true (Esnoc Enil i (▷ Q)%I) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ?? HQ. rewrite -(always_elim Q) -(löb (□ Q)) -always_later.
  apply impl_intro_l, (always_intro _ _).
  rewrite envs_app_sound //; simpl.
  by rewrite right_id always_and_sep_l' wand_elim_r HQ.
Qed.

(** * Always *)
Lemma tac_always_intro Δ Q :
  (envs_clear_spatial Δ ⊢ Q) → Δ ⊢ □ Q.
Proof.
  intros <-. rewrite envs_clear_spatial_sound sep_elim_l.
  by apply (always_intro _ _).
Qed.

Lemma tac_persistent Δ Δ' i p P P' Q :
  envs_lookup i Δ = Some (p, P) → IntoPersistentP P P' →
  envs_replace i p true (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ??? <-. rewrite envs_replace_sound //; simpl.
  by rewrite right_id (into_persistentP P) always_if_always wand_elim_r.
Qed.

(** * Implication and wand *)
Lemma tac_impl_intro Δ Δ' i P Q :
  (if env_spatial_is_nil Δ then Unit else PersistentP P) →
  envs_app false (Esnoc Enil i P) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ P → Q.
Proof.
  intros ?? <-. destruct (env_spatial_is_nil Δ) eqn:?.
  - rewrite (persistentP Δ) envs_app_sound //; simpl.
    by rewrite right_id always_wand_impl always_elim.
  - apply impl_intro_l. rewrite envs_app_sound //; simpl.
    by rewrite always_and_sep_l right_id wand_elim_r.
Qed.
Lemma tac_impl_intro_persistent Δ Δ' i P P' Q :
  IntoPersistentP P P' →
  envs_app true (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ P → Q.
Proof.
  intros ?? HQ. rewrite envs_app_sound //; simpl. apply impl_intro_l.
  by rewrite right_id {1}(into_persistentP P) always_and_sep_l wand_elim_r.
Qed.
Lemma tac_pure_impl_intro Δ (φ ψ : Prop) :
  (φ → Δ ⊢ ⌜ψ⌝) → Δ ⊢ ⌜φ → ψ⌝.
Proof. intros. rewrite pure_impl. by apply impl_intro_l, pure_elim_l. Qed.
Lemma tac_impl_intro_pure Δ P φ Q : IntoPure P φ → (φ → Δ ⊢ Q) → Δ ⊢ P → Q.
Proof.
  intros. by apply impl_intro_l; rewrite (into_pure P); apply pure_elim_l.
Qed.
Lemma tac_impl_intro_drop Δ P Q : (Δ ⊢ Q) → Δ ⊢ P → Q.
Proof. intros. apply impl_intro_l. by rewrite and_elim_r. Qed.

Lemma tac_wand_intro Δ Δ' i P Q :
  envs_app false (Esnoc Enil i P) Δ = Some Δ' → (Δ' ⊢ Q) → Δ ⊢ P -∗ Q.
Proof.
  intros ? HQ. rewrite envs_app_sound //; simpl. by rewrite right_id HQ.
Qed.
Lemma tac_wand_intro_persistent Δ Δ' i P P' Q :
  IntoPersistentP P P' →
  envs_app true (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ P -∗ Q.
Proof.
  intros. rewrite envs_app_sound //; simpl.
  rewrite right_id. by apply wand_mono.
Qed.
Lemma tac_wand_intro_pure Δ P φ Q : IntoPure P φ → (φ → Δ ⊢ Q) → Δ ⊢ P -∗ Q.
Proof.
  intros. by apply wand_intro_l; rewrite (into_pure P); apply pure_elim_sep_l.
Qed.
Lemma tac_wand_intro_drop Δ P Q : (Δ ⊢ Q) → Δ ⊢ P -∗ Q.
Proof. intros. apply wand_intro_l. by rewrite sep_elim_r. Qed.

(* This is pretty much [tac_specialize_assert] with [js:=[j]] and [tac_exact],
but it is doing some work to keep the order of hypotheses preserved. *)
Lemma tac_specialize Δ Δ' Δ'' i p j q P1 P2 R Q :
  envs_lookup_delete i Δ = Some (p, P1, Δ') →
  envs_lookup j (if p then Δ else Δ') = Some (q, R) →
  IntoWand p R P1 P2 →
  match p with
  | true  => envs_simple_replace j q (Esnoc Enil j P2) Δ
  | false => envs_replace j q false (Esnoc Enil j P2) Δ'
             (* remove [i] and make [j] spatial *)
  end = Some Δ'' →
  (Δ'' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ??? <-. destruct p.
  - rewrite envs_lookup_persistent_sound // envs_simple_replace_sound //; simpl.
    rewrite right_id assoc (into_wand _ R) /=. destruct q; simpl.
    + by rewrite always_wand always_always !wand_elim_r.
    + by rewrite !wand_elim_r.
  - rewrite envs_lookup_sound //; simpl.
    rewrite envs_lookup_sound // (envs_replace_sound' _ Δ'') //; simpl.
    by rewrite right_id assoc (into_wand _ R) always_if_elim wand_elim_r wand_elim_r.
Qed.

Lemma tac_specialize_assert Δ Δ' Δ1 Δ2' j q lr js R P1 P2 P1' Q :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand false R P1 P2 → ElimModal P1' P1 Q Q →
  ('(Δ1,Δ2) ← envs_split lr js Δ';
    Δ2' ← envs_app false (Esnoc Enil j P2) Δ2;
    Some (Δ1,Δ2')) = Some (Δ1,Δ2') → (* does not preserve position of [j] *)
  (Δ1 ⊢ P1') → (Δ2' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ??? HP1 HQ.
  destruct (envs_split _ _ _) as [[? Δ2]|] eqn:?; simplify_eq/=;
    destruct (envs_app _ _ _) eqn:?; simplify_eq/=.
  rewrite envs_lookup_sound // envs_split_sound //.
  rewrite (envs_app_sound Δ2) //; simpl.
  rewrite right_id (into_wand _ R) HP1 assoc -(comm _ P1') -assoc.
  rewrite -(elim_modal P1' P1 Q Q). apply sep_mono_r, wand_intro_l.
  by rewrite always_if_elim assoc !wand_elim_r.
Qed.

Lemma tac_unlock P Q : (P ⊢ Q) → P ⊢ locked Q.
Proof. by unlock. Qed.

Lemma tac_specialize_frame Δ Δ' j q R P1 P2 P1' Q Q' :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand false R P1 P2 →
  ElimModal P1' P1 Q Q →
  (Δ' ⊢ P1' ∗ locked Q') →
  Q' = (P2 -∗ Q)%I →
  Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ?? HPQ ->.
  rewrite envs_lookup_sound //. rewrite HPQ -lock.
  rewrite (into_wand _ R) assoc -(comm _ P1') -assoc always_if_elim.
  rewrite -{2}(elim_modal P1' P1 Q Q). apply sep_mono_r, wand_intro_l.
  by rewrite assoc !wand_elim_r.
Qed.

Lemma tac_specialize_assert_pure Δ Δ' j q R P1 P2 φ Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand false R P1 P2 → FromPure P1 φ →
  envs_simple_replace j q (Esnoc Enil j P2) Δ = Some Δ' →
  φ → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id (into_wand _ R) -(from_pure P1) pure_True //.
  by rewrite wand_True wand_elim_r.
Qed.

Lemma tac_specialize_assert_persistent Δ Δ' Δ'' j q P1 P2 R Q :
  envs_lookup_delete j Δ = Some (q, R, Δ') →
  IntoWand false R P1 P2 → PersistentP P1 →
  envs_simple_replace j q (Esnoc Enil j P2) Δ = Some Δ'' →
  (Δ' ⊢ P1) → (Δ'' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ??? HP1 <-.
  rewrite envs_lookup_sound //.
  rewrite -(idemp uPred_and (envs_delete _ _ _)).
  rewrite {1}HP1 (persistentP P1) always_and_sep_l assoc.
  rewrite envs_simple_replace_sound' //; simpl.
  rewrite right_id (into_wand _ R) (always_elim_if q) -always_if_sep wand_elim_l.
  by rewrite wand_elim_r.
Qed.

Lemma tac_specialize_persistent_helper Δ Δ' j q P R Q :
  envs_lookup j Δ = Some (q,P) →
  (Δ ⊢ R) → PersistentP R →
  envs_replace j q true (Esnoc Enil j R) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ? HR ?? <-.
  rewrite -(idemp uPred_and Δ) {1}HR always_and_sep_l.
  rewrite envs_replace_sound //; simpl.
  by rewrite right_id assoc (sep_elim_l R) always_always wand_elim_r.
Qed.

Lemma tac_revert Δ Δ' i p P Q :
  envs_lookup_delete i Δ = Some (p,P,Δ') →
  (Δ' ⊢ (if p then □ P else P) -∗ Q) → Δ ⊢ Q.
Proof.
  intros ? HQ. rewrite envs_lookup_delete_sound //; simpl.
  by rewrite HQ /uPred_always_if wand_elim_r.
Qed.

Lemma tac_revert_ih Δ P Q :
  env_spatial_is_nil Δ = true →
  (of_envs Δ ⊢ P) →
  (of_envs Δ ⊢ □ P → Q) →
  (of_envs Δ ⊢ Q).
Proof.
  intros ? HP HPQ.
  by rewrite -(idemp uPred_and Δ) {1}(persistentP Δ) {1}HP HPQ impl_elim_r.
Qed.

Lemma tac_assert Δ Δ1 Δ2 Δ2' lr js j P P' Q :
  ElimModal P' P Q Q →
  envs_split lr js Δ = Some (Δ1,Δ2) →
  envs_app false (Esnoc Enil j P) Δ2 = Some Δ2' →
  (Δ1 ⊢ P') → (Δ2' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ??? HP HQ. rewrite envs_split_sound //.
  rewrite (envs_app_sound Δ2) //; simpl.
  by rewrite right_id HP HQ.
Qed.

Lemma tac_assert_persistent Δ Δ1 Δ2 Δ' lr js j P Q :
  envs_split lr js Δ = Some (Δ1,Δ2) →
  envs_app false (Esnoc Enil j P) Δ = Some Δ' →
  PersistentP P →
  (Δ1 ⊢ P) → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ??? HP <-. rewrite -(idemp uPred_and Δ) {1}envs_split_sound //.
  rewrite HP sep_elim_l (always_and_sep_l P) envs_app_sound //; simpl.
  by rewrite right_id wand_elim_r.
Qed.

Lemma tac_assert_pure Δ Δ' j P φ Q :
  envs_app false (Esnoc Enil j P) Δ = Some Δ' →
  FromPure P φ →
  φ → (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ??? <-. rewrite envs_app_sound //; simpl.
  by rewrite right_id -(from_pure P) pure_True // -always_impl_wand True_impl.
Qed.

Lemma tac_pose_proof Δ Δ' j P Q :
  P →
  envs_app true (Esnoc Enil j P) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros HP ? <-. rewrite envs_app_sound //; simpl.
  by rewrite right_id -HP always_pure wand_True.
Qed.

Lemma tac_pose_proof_hyp Δ Δ' Δ'' i p j P Q :
  envs_lookup_delete i Δ = Some (p, P, Δ') →
  envs_app p (Esnoc Enil j P) (if p then Δ else Δ') = Some Δ'' →
  (Δ'' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros [? ->]%envs_lookup_delete_Some ? <-. destruct p.
  - rewrite envs_lookup_persistent_sound // envs_app_sound //; simpl.
    by rewrite right_id wand_elim_r.
  - rewrite envs_lookup_sound // envs_app_sound //; simpl.
    by rewrite right_id wand_elim_r.
Qed.

Lemma tac_apply Δ Δ' i p R P1 P2 :
  envs_lookup_delete i Δ = Some (p, R, Δ') → IntoWand false R P1 P2 →
  (Δ' ⊢ P1) → Δ ⊢ P2.
Proof.
  intros ?? HP1. rewrite envs_lookup_delete_sound' //.
  by rewrite (into_wand _ R) HP1 wand_elim_l.
Qed.

(** * Rewriting *)
Lemma tac_rewrite Δ i p Pxy (lr : bool) Q :
  envs_lookup i Δ = Some (p, Pxy) →
  ∀ {A : ofeT} (x y : A) (Φ : A → uPred M),
    (Pxy ⊢ x ≡ y) →
    (Q ⊣⊢ Φ (if lr then y else x)) →
    (NonExpansive Φ) →
    (Δ ⊢ Φ (if lr then x else y)) → Δ ⊢ Q.
Proof.
  intros ? A x y ? HPxy -> ?; apply internal_eq_rewrite; auto.
  rewrite {1}envs_lookup_sound' //; rewrite sep_elim_l HPxy.
  destruct lr; auto using internal_eq_sym.
Qed.

Lemma tac_rewrite_in Δ i p Pxy j q P (lr : bool) Q :
  envs_lookup i Δ = Some (p, Pxy) →
  envs_lookup j Δ = Some (q, P) →
  ∀ {A : ofeT} Δ' x y (Φ : A → uPred M),
    (Pxy ⊢ x ≡ y) →
    (P ⊣⊢ Φ (if lr then y else x)) →
    (NonExpansive Φ) →
    envs_simple_replace j q (Esnoc Enil j (Φ (if lr then x else y))) Δ = Some Δ' →
    (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ?? A Δ' x y Φ HPxy HP ?? <-.
  rewrite -(idemp uPred_and Δ) {2}(envs_lookup_sound' _ i) //.
  rewrite sep_elim_l HPxy always_and_sep_r.
  rewrite (envs_simple_replace_sound _ _ j) //; simpl.
  rewrite HP right_id -assoc; apply wand_elim_r'. destruct lr.
  - apply (internal_eq_rewrite x y (λ y, □?q Φ y -∗ Δ')%I);
      eauto with I. solve_proper.
  - apply (internal_eq_rewrite y x (λ y, □?q Φ y -∗ Δ')%I);
      eauto using internal_eq_sym with I.
    solve_proper.
Qed.

(** * Conjunction splitting *)
Lemma tac_and_split Δ P Q1 Q2 :
  FromAnd true P Q1 Q2 → (Δ ⊢ Q1) → (Δ ⊢ Q2) → Δ ⊢ P.
Proof. intros. rewrite -(from_and true P). by apply and_intro. Qed.

(** * Separating conjunction splitting *)
Lemma tac_sep_split Δ Δ1 Δ2 lr js P Q1 Q2 :
  FromAnd false P Q1 Q2 →
  envs_split lr js Δ = Some (Δ1,Δ2) →
  (Δ1 ⊢ Q1) → (Δ2 ⊢ Q2) → Δ ⊢ P.
Proof.
  intros. rewrite envs_split_sound // -(from_and false P). by apply sep_mono.
Qed.

(** * Combining *)
Class FromSeps {M} (P : uPred M) (Qs : list (uPred M)) :=
  from_seps : [∗] Qs ⊢ P.
Arguments from_seps {_} _ _ {_}.

Global Instance from_seps_nil : @FromSeps M True [].
Proof. done. Qed.
Global Instance from_seps_singleton P : FromSeps P [P] | 1.
Proof. by rewrite /FromSeps /= right_id. Qed.
Global Instance from_seps_cons P P' Q Qs :
  FromSeps P' Qs → FromAnd false P Q P' → FromSeps P (Q :: Qs) | 2.
Proof. by rewrite /FromSeps /FromAnd /= => ->. Qed.

Lemma tac_combine Δ1 Δ2 Δ3 js p Ps j P Q :
  envs_lookup_delete_list js false Δ1 = Some (p, Ps, Δ2) →
  FromSeps P Ps →
  envs_app p (Esnoc Enil j P) Δ2 = Some Δ3 →
  (Δ3 ⊢ Q) → Δ1 ⊢ Q.
Proof.
  intros ??? <-. rewrite envs_lookup_delete_list_sound //.
  rewrite from_seps. rewrite envs_app_sound //; simpl.
  by rewrite right_id wand_elim_r.
Qed.

(** * Conjunction/separating conjunction elimination *)
Lemma tac_and_destruct Δ Δ' i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) → IntoAnd p P P1 P2 →
  envs_simple_replace i p (Esnoc (Esnoc Enil j1 P1) j2 P2) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //; simpl. rewrite (into_and p P).
  by destruct p; rewrite /= ?right_id (comm _ P1) ?always_and_sep wand_elim_r.
Qed.

(* Using this tactic, one can destruct a (non-separating) conjunction in the
spatial context as long as one of the conjuncts is thrown away. It corresponds
to the principle of "external choice" in linear logic. *)
Lemma tac_and_destruct_choice Δ Δ' i p (lr : bool) j P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) → IntoAnd true P P1 P2 →
  envs_simple_replace i p (Esnoc Enil j (if lr then P1 else P2)) Δ = Some Δ' →
  (Δ' ⊢ Q) → Δ ⊢ Q.
Proof.
  intros. rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id (into_and true P). destruct lr.
  - by rewrite and_elim_l wand_elim_r.
  - by rewrite and_elim_r wand_elim_r.
Qed.

(** * Framing *)
Lemma tac_frame_pure Δ (φ : Prop) P Q :
  φ → Frame true ⌜φ⌝ P Q → (Δ ⊢ Q) → Δ ⊢ P.
Proof.
  intros ?? ->. by rewrite -(frame ⌜φ⌝ P) /= always_pure pure_True // left_id.
Qed.

Lemma tac_frame Δ Δ' i p R P Q :
  envs_lookup_delete i Δ = Some (p, R, Δ') → Frame p R P Q →
  ((if p then Δ else Δ') ⊢ Q) → Δ ⊢ P.
Proof.
  intros [? ->]%envs_lookup_delete_Some ? HQ. destruct p.
  - by rewrite envs_lookup_persistent_sound // -(frame R P) HQ.
  - rewrite envs_lookup_sound //; simpl. by rewrite -(frame R P) HQ.
Qed.

(** * Disjunction *)
Lemma tac_or_l Δ P Q1 Q2 : FromOr P Q1 Q2 → (Δ ⊢ Q1) → Δ ⊢ P.
Proof. intros. rewrite -(from_or P). by apply or_intro_l'. Qed.
Lemma tac_or_r Δ P Q1 Q2 : FromOr P Q1 Q2 → (Δ ⊢ Q2) → Δ ⊢ P.
Proof. intros. rewrite -(from_or P). by apply or_intro_r'. Qed.

Lemma tac_or_destruct Δ Δ1 Δ2 i p j1 j2 P P1 P2 Q :
  envs_lookup i Δ = Some (p, P) → IntoOr P P1 P2 →
  envs_simple_replace i p (Esnoc Enil j1 P1) Δ = Some Δ1 →
  envs_simple_replace i p (Esnoc Enil j2 P2) Δ = Some Δ2 →
  (Δ1 ⊢ Q) → (Δ2 ⊢ Q) → Δ ⊢ Q.
Proof.
  intros ???? HP1 HP2. rewrite envs_lookup_sound //.
  rewrite (into_or P) always_if_or sep_or_r; apply or_elim.
  - rewrite (envs_simple_replace_sound' _ Δ1) //.
    by rewrite /= right_id wand_elim_r.
  - rewrite (envs_simple_replace_sound' _ Δ2) //.
    by rewrite /= right_id wand_elim_r.
Qed.

(** * Forall *)
Lemma tac_forall_intro {A} Δ (Φ : A → uPred M) : (∀ a, Δ ⊢ Φ a) → Δ ⊢ ∀ a, Φ a.
Proof. apply forall_intro. Qed.

Lemma tac_pure_forall_intro {A} Δ (φ : A → Prop) :
  (∀ a, Δ ⊢ ⌜φ a⌝) → Δ ⊢ ⌜∀ a, φ a⌝.
Proof. intros. rewrite pure_forall. by apply forall_intro. Qed.

Lemma tac_forall_specialize {A} Δ Δ' i p P (Φ : A → uPred M) Q :
  envs_lookup i Δ = Some (p, P) → IntoForall P Φ →
  (∃ x : A,
    envs_simple_replace i p (Esnoc Enil i (Φ x)) Δ = Some Δ' ∧
    (Δ' ⊢ Q)) →
  Δ ⊢ Q.
Proof.
  intros ?? (x&?&?). rewrite envs_simple_replace_sound //; simpl.
  by rewrite right_id (into_forall P) (forall_elim x) wand_elim_r.
Qed.

Lemma tac_forall_revert {A} Δ (Φ : A → uPred M) :
  (Δ ⊢ ∀ a, Φ a) → ∀ a, Δ ⊢ Φ a.
Proof. intros HΔ a. by rewrite HΔ (forall_elim a). Qed.

(** * Existential *)
Lemma tac_exist {A} Δ P (Φ : A → uPred M) :
  FromExist P Φ → (∃ a, Δ ⊢ Φ a) → Δ ⊢ P.
Proof. intros ? [a ?]. rewrite -(from_exist P). eauto using exist_intro'. Qed.

Lemma tac_exist_destruct {A} Δ i p j P (Φ : A → uPred M) Q :
  envs_lookup i Δ = Some (p, P) → IntoExist P Φ →
  (∀ a, ∃ Δ',
    envs_simple_replace i p (Esnoc Enil j (Φ a)) Δ = Some Δ' ∧ (Δ' ⊢ Q)) →
  Δ ⊢ Q.
Proof.
  intros ?? HΦ. rewrite envs_lookup_sound //.
  rewrite (into_exist P) always_if_exist sep_exist_r.
  apply exist_elim=> a; destruct (HΦ a) as (Δ'&?&?).
  rewrite envs_simple_replace_sound' //; simpl. by rewrite right_id wand_elim_r.
Qed.

(** * Modalities *)
Lemma tac_modal_intro Δ P Q : FromModal P Q → (Δ ⊢ Q) → Δ ⊢ P.
Proof. rewrite /FromModal. by intros <- ->. Qed.

Lemma tac_modal_elim Δ Δ' i p P' P Q Q' :
  envs_lookup i Δ = Some (p, P) →
  ElimModal P P' Q Q' →
  envs_replace i p false (Esnoc Enil i P') Δ = Some Δ' →
  (Δ' ⊢ Q') → Δ ⊢ Q.
Proof.
  intros ??? HΔ. rewrite envs_replace_sound //; simpl.
  rewrite right_id HΔ always_if_elim. by apply elim_modal.
Qed.
End tactics.
