From iris.algebra Require Import stepindex ofe cmra.
From iris.prelude Require Import options.

(** * [indexT] instance for [nat] *)
(** This file provides an instantiation of the [indexT] stepindex type for [nat],
   which is the stepindex type traditionally used by Iris. *)
(** Side-effect: every development importing this file will automatically use finite indices
    due to the declared instances and canonical structures for [indexT]. *)

Lemma nat_index_mixin : IndexMixin nat lt le 0 S.
Proof.
  constructor; try lia.
  - typeclasses eauto.
  - exact lt_wf.
  - intros m n. destruct (lt_eq_lt_dec m n) as [[]|]; eauto.
  - intros [|n].
    + right; intros; lia.
    + left; by (exists n).
Qed.
(** This declares the globally used index type to be [natI].
    All following lemmas are implicitly specialized to [natI]! *)
Canonical Structure natI : indexT := IndexT nat lt le 0 S nat_index_mixin.
Global Existing Instance natI | 0.

Global Instance nat_finite_index : FiniteIndex natI.
Proof. intros [|n]; eauto. Qed.


(** We define a notion of finite OFEs and COFEs that matches Iris's traditional definitions,
  and makes it easier to define OFEs and COFEs specialized to the [natI] index type. *)
Section finite_ofes.
  Local Set Default Proof Using "Type*".

  Lemma dist_later_S {A : ofe} (n : nat) (a b: A) : a ≡{n}≡ b ↔ dist_later (S n) a b.
  Proof. apply dist_later_S. Qed.

  Lemma dist_S {A: ofe} n (x y: A) : x ≡{S n}≡ y → x ≡{n}≡ y.
  Proof. apply dist_S. Qed.

  Lemma fin_dist_le {A : ofe} (n m : nat) (x y : A) : x ≡{n}≡ y → m ≤ n → x ≡{m}≡ y.
  Proof. intros ??; eapply dist_le; done. Qed.

  Lemma contractive_0 {A B : ofe} (f : A → B) `{!Contractive f} x y : f x ≡{0}≡ f y.
  Proof. apply (_ : Contractive f), dist_later_0. Qed.
  Lemma contractive_S {A B : ofe} (f : A → B) `{!Contractive f} (n : nat) x y : x ≡{n}≡ y → f x ≡{S n}≡ f y.
  Proof. intros. by apply (_ : Contractive f), dist_later_S. Qed.

  (** We define [dist_later_fin], an equivalent (see dist_later_fin_iff) version of
     [dist_later] that uses a [match] on the step-index instead of the
     quantification over smaller step-indicies. The definition of [dist_later_fin]
     matches how [dist_later] used to be defined (i.e., with a [match] on the
     step-index), so [dist_later_fin] simplifies adapting existing Iris
     developments that used to rely on the reduction behavior of [dist_later].

     The "fin" indicates that when, in the future, the step-index is abstracted away,
     this equivalence will only hold for finite step-indices (as in, ordinals without
     "limit" steps such as natural numbers).
  *)
  Definition dist_later_fin {A : ofe} (n : nat) (x y : A) :=
    match n with 0 => True | S n => x ≡{n}≡ y end.

  Lemma dist_later_fin_iff {A : ofe} (n : nat) (x y : A):
    dist_later n x y ↔ dist_later_fin n x y.
  Proof.
    destruct n; unfold dist_later_fin; first by split; eauto using dist_later_0.
    by rewrite dist_later_S.
  Qed.

  Lemma dist_later_0 {A : ofe} (a b : A): dist_later 0 a b.
  Proof. apply (@dist_later_0 natI). Qed.

  (** Derived lemma about the completion *)
  Lemma conv_compl' {A : ofe} `{!Cofe A} n (c : chain A) : compl c ≡{n}≡ c (S n).
  Proof.
    eapply conv_compl_le; stepindex using index_succ_greater.
  Qed.

  (** [nat] has no non-trivial limit indices *)
  Lemma finite_index_no_limit (n : nat): ¬ index_is_proper_limit n.
  Proof.
    intros Hlim. destruct Hlim as [Hlim Hnz].
    destruct n as [|n]; simpl in Hnz; first lia.
    eapply index_succ_not_limit, Hlim.
  Qed.

  Global Instance bounded_limit_preserving {A : ofe} `{!Cofe A} (P : A → Prop) : BoundedLimitPreserving P.
  Proof.
    intros n Hlim. exfalso. by eapply finite_index_no_limit.
  Qed.

  (** Shorthand for defining OFEs that only work for [natI] *)
  Record FiniteOfeMixin A `{!Equiv A, !Dist A} := {
    finite_mixin_equiv_dist (x y : A) : x ≡ y ↔ ∀ n, x ≡{n}≡ y;
    finite_mixin_dist_equivalence n : Equivalence (@dist natI A _ n);
    finite_mixin_dist_S n (x y : A) : x ≡{S n}≡ y → x ≡{n}≡ y
  }.

  Lemma finite_ofe_to_ofe_mixin {A} `{!Equiv A, !Dist A} (M : FiniteOfeMixin A) : OfeMixin A.
  Proof.
    split; [apply M..|].
    intros n m x y Heq Hlt.
    induction Hlt; eauto using finite_mixin_dist_S.
  Qed.

  Definition FiniteOfe A `{!Equiv A, !Dist A} (M : FiniteOfeMixin A) :=
    Ofe A (finite_ofe_to_ofe_mixin M).

  (** Shorthand for defining COFEs that only work for [natI] *)
  Class FiniteCofe (A : ofe) := {
    fcompl : Compl A;
    conv_fcompl n c : fcompl c ≡{n}≡ c n;
  }.
  Global Arguments fcompl : simpl never.

  (** For natural numbers, the bounded completion [lbcompl] is obtained for free *)
  Definition flbcompl (A : ofe) (n : nat) : LBCompl A n :=
    λ Hn, match finite_index_no_limit _ Hn with end.

  Global Program Instance cofe_from_finite_cofe {A : ofe} `{!FiniteCofe A} : Cofe A :=
    {| compl := fcompl; lbcompl := flbcompl A |}.
  Next Obligation.
    intros ????. apply conv_fcompl.
  Qed.
  Next Obligation.
    intros ???????. rewrite /flbcompl.
    by destruct finite_index_no_limit.
  Qed.
  Next Obligation.
    intros ????????. rewrite /flbcompl.
    by destruct finite_index_no_limit.
  Qed.

  Section iso_fin_cofe_subtype.
    Context {A B : ofe} `{!Cofe A} (P : A → Prop) (f : ∀ x, P x → B) (g : B → A).
    Context (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2).
    Let Hgne : NonExpansive g := λ n y1 y2, proj1 (g_dist n y1 y2).
    Local Existing Instance Hgne.
    Context (gf : ∀ x Hx, g (f x Hx) ≡ x).
    Context (Hlimit : ∀ c : chain B, P (compl (chain_map g c))).
    Program Definition iso_finite_cofe_subtype : FiniteCofe B :=
      {| fcompl c := f (compl (chain_map g c)) _ |}.
    Next Obligation. apply Hlimit. Qed.
    Next Obligation. intros n c; simpl. apply g_dist. by rewrite gf conv_compl. Qed.
  End iso_fin_cofe_subtype.

  Lemma iso_finite_cofe_subtype' {A B : ofe} `{!Cofe A}
    (P : A → Prop) (f : ∀ x, P x → B) (g : B → A)
    (Pg : ∀ y, P (g y))
    (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
    (gf : ∀ x Hx, g (f x Hx) ≡ x)
    (Hlimit : LimitPreserving P) : Cofe B.
  Proof.
    apply: cofe_from_finite_cofe.
    apply: (iso_finite_cofe_subtype P f g); eauto.
  Qed.

  Definition iso_finite_cofe {A B : ofe} `{!Cofe A} (f : A → B) (g : B → A)
    (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
    (gf : ∀ x, g (f x) ≡ x) : Cofe B.
  Proof.
    apply: cofe_from_finite_cofe.
    by apply (iso_finite_cofe_subtype (λ _, True) (λ x _, f x) g).
  Qed.
End finite_ofes.

(**
  For backwards compatibility, we also define the tactic [f_contractive_fin] that
  works with [dist_later_fin]. The
  new version of [f_contractive] is future proof with respect to generalizing the
  type of step-indices, while the old tactic relies crucially on the step-indices
  being [nat] and the reduction behavior of [dist_later]. The tactic [f_contractive_fin]
  simplifies backwards compatibility of existing Iris developments (e.g., RustBelt),
  that define custom notions of [dist] and [dist_later] but should be avoided if
  possible. *)

(** The tactic [dist_later_fin_intro] is a special case of [dist_later_intro] which only works for
   natural numbers as step-indices. It changes [dist_later] to [dist_later_fin],
   which only makes sense on natural numbers. We keep [dist_later_fin_intro]
   around for backwards compatibility. *)
(** For the goal [dist_later n x y], the tactic [dist_later_fin_intro] changes
the goal to [dist_later_fin] and takes care of the case where [n=0], such
that we are only left with the case where [n = S n'] for some [n']. Changing
[dist_later] to [dist_later_fin] enables reduction and thus works better with
custom versions of [dist] as used e.g. by LambdaRust. *)
Ltac dist_later_fin_intro :=
  match goal with
  | |- @dist_later ?A _ ?n ?x ?y =>
      apply dist_later_fin_iff;
      destruct n as [|n]; [exact I|change (@dist natI A _ n x y)]
  end.
Tactic Notation "f_contractive_fin" :=
  f_contractive_prepare;
  try dist_later_fin_intro;
  try fast_reflexivity.

(** Derived lemmas about CMRAs for [natI] *)
Section finite_cmras.
  Context {A : cmra}.

  Lemma cmra_validN_S n (x : A) : ✓{S n} x → ✓{n} x.
  Proof.
    intros ?. eapply cmra_validN_downward; stepindex using index_succ_greater.
  Qed.

  Lemma cmra_includedN_S n (x y : A): x ≼{S n} y → x ≼{n} y.
  Proof. apply cmra_includedN_S. Qed.

  Lemma cmra_includedN_le (n m : nat) (x y : A) : x ≼{n} y → m ≤ n → x ≼{m} y.
  Proof. by intros [z Hz] H; exists z; eapply dist_le. Qed.

  Lemma cmra_validN_le (n n' : nat) (x : A) : ✓{n} x → n' ≤ n → ✓{n'} x.
  Proof.
    intros ??; eapply cmra.cmra_validN_le; done.
  Qed.
End finite_cmras.
