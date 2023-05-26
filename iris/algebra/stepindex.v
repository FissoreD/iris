From iris.prelude Require Export prelude.
From iris.prelude Require Import options.
Set Primitive Projections.

(** Step-Indices

  In this file, we declare an interface for step-indices (see [indexT]).
  Step-indexing in Iris enables all kinds of recursive constructions such
  as mixed-variance recursive definitions and mixed-variance recursive types.
  For more information on step-indexing and how it is used in Iris, see the
  journal paper "Iris from the Ground Up" (which can be found here
  https://www.cambridge.org/core/journals/journal-of-functional-programming/article/iris-from-the-ground-up-a-modular-foundation-for-higherorder-concurrent-separation-logic/26301B518CE2C52796BFA12B8BAB5B5F)
  or the Iris appendix.

  Traditionally, step-indexing is done by using natural numbers as indices.
  However, it can also be generalized to richer sets of indices such as omega^2
  (i.e., pairs of natural numbers with lexicographic ordering), omega^omega
  (i.e., lists of natural numbers with lexicographic ordering), countable
  ordinals, and even uncountable ordinals. Large parts of Iris are agnostic of
  the step-indexing type that is used, which allows us to factor out the notion
  of a step-index via the interface of an "index type" (see [indexT] and
  [IndexMixin]) and define them generically in the index type (e.g., the
  [algebra] folder).

  Note that transfinite step-indexing is not a strict improvement on finite
  step-indexing (i.e., step-indexing with natural numbers)—they are incomparable
  (see the paper on "Transfinite Iris" for an explanation of the trade-offs,
  which can be found here https://dl.acm.org/doi/10.1145/3453483.3454031).
  Thus, to retain the benefits of both, we make definitions parametric instead
  of specialized to natural numbers or a particular type of ordinals.
*)


(** An index type [I] comes with
    - a well-founded strict linear order [ilt] (written [i ≺ᵢ j]),
    - a total linear order [ile] (written [i ⪯ᵢ j]),
    - a zero index [zero],
    - and a successor operation on indices [succ].

    The less-or-equal operation [ile] must be compatible with the less-than
    operation [ilt] operation. That is, [i ⪯ᵢ j] iff [i ≺ᵢ j] or [i = j]. The
    [zero] index has to be the smallest step-index (i.e., [¬ i ≺ zero] for all [i])
    and the successor operation [succ] should yield for a step-index [i] the least index
    greater than [i]. The total order [ilt] should be _computationally_ decidable,
    and, finally, it should be computationally decidable whether a given step-index
    is a limit index (i.e., it cannot be reached from any predecessor by applying
    the successor operation).

    The less-or-equal operation [ile] is not strictly necessary since [i ⪯ᵢ j] is equivalent
    to  [i ≺ᵢ j] or [i = j]. We add it as an additional parameter to this interface for
    engineering reasons: the addition of [ile] simplifies backwards compatibly to developments
    that assume step-indices are always natural numbers and (implicitly) that [i ⪯ᵢ j] unifies
    with [i ≤ j] for natural numbers.
  *)
Record IndexMixin {I}
    {ilt : I → I → Prop} {ile : I → I → Prop} {zero : I} {succ : I → I} := {
  index_mixin_lt_trans : Transitive ilt;
  index_mixin_lt_wf : well_founded ilt;
  index_mixin_lt_strict_total n m : (ilt n m) + (n = m) + (ilt m n);
  index_mixin_le_lt_iff n m : ile n m ↔ ilt n m ∨ n = m;
  index_mixin_zero_least n : ¬ ilt n zero;
  index_mixin_succ_greater n : ilt n (succ n);
  index_mixin_succ_least n m : ilt n m → ile (succ n) m;
  index_mixin_dec_limit n :
    {m | n = succ m} + (∀ m, ilt m n → ilt (succ m) n);
}.
Global Arguments IndexMixin : clear implicits.

(** [indexT] is both a canonical structure and a typeclass.
    When working with a concrete index type, we usually fix it globally.
    Declaring an appropriate instance and structure enables Coq to infer
    the globally fixed index type automatically in almost all places.
    For an example of how to instantiate this, consider [finite_stepindex.v].

    Using both a canonical structure and a type class is not very common. In
    this case, it maximizes the inference that is done by Coq when we use the
    index type. The fact that the step-index is a type class makes sure in, for
    example, lemma statements that it will be inferred from the context
    automatically. It also means that if we work with finite step-indices then
    the finite step-index instance will be used by default as soon
    as we (or any of our dependencies) import [finite_stepindex.v].
    The canonical structure, on the other hand, makes sure that the index type
    is inferred automatically as soon as we use either natural numbers or
    ordinals as the step-index in a concrete lemma.
*)
Structure indexT := IndexT {
  index : Type;
  index_lt : relation index;
  index_le : relation index;
  index_zero : index;
  index_succ : index → index;
  index_mixin : IndexMixin index index_lt index_le index_zero index_succ;
}.

Existing Class indexT.
Global Arguments index {_}.
Global Arguments index_lt {_}.
Global Arguments index_le {_}.
Global Arguments index_zero {_}.
Global Arguments index_succ {_} _.

Notation "(≺ᵢ)" := (index_lt).
Notation "(≻ᵢ)" := (flip (index_lt)).

Notation zero := (index_zero).
Notation succ n := (index_succ n).
Notation "n '≺ᵢ' m" := (index_lt n m) (at level 60).

Notation "(⪯ᵢ)" := (index_le).
Notation "n '⪯ᵢ' m" := (index_le n m) (at level 60).

(* lifting of the mixin properties *)
Section index_laws.
  Context `{SI : indexT}.
  Global Instance index_lt_trans : Transitive (index_lt).
  Proof. eapply index_mixin_lt_trans, index_mixin. Qed.
  Lemma index_lt_wf : well_founded (index_lt).
  Proof. eapply index_mixin_lt_wf, index_mixin. Qed.
  Lemma index_lt_eq_lt_dec (n m : index) : (n ≺ᵢ m) + (n = m) + (m ≺ᵢ n).
  Proof. eapply index_mixin_lt_strict_total, index_mixin. Qed.
  Lemma index_le_lt_iff (n m : index) : n ⪯ᵢ m ↔ n ≺ᵢ m ∨ n = m.
  Proof. eapply index_mixin_le_lt_iff, index_mixin. Qed.
  Lemma index_zero_least n : ¬ n ≺ᵢ zero.
  Proof. eapply index_mixin_zero_least, index_mixin. Qed.
  Lemma index_succ_greater (n : index) : n ≺ᵢ succ n.
  Proof. eapply index_mixin_succ_greater, index_mixin. Qed.
  Lemma index_succ_least (n m : index) : n ≺ᵢ m → succ n ⪯ᵢ m.
  Proof. eapply index_mixin_succ_least, index_mixin. Qed.
  Lemma index_dec_limit (n : index) :
    { m | n = succ m } + (∀ m, m ≺ᵢ n → succ m ≺ᵢ n).
  Proof. eapply index_mixin_dec_limit, index_mixin. Qed.
End index_laws.

(** Limit indices *)
Definition index_is_limit {SI : indexT} (n : index) := ∀ m, m ≺ᵢ n → succ m ≺ᵢ n.

(** Proper limit indices [limit_idx]

    According to [index_is_limit], [zero] is a limit index. In many definitions
    and proofs, it is helpful to think of zero as a special case rather than a
    degenerate limit index. We therefore define the notion of a proper limit
    index, which is a limit index that is greater than zero.
*)
Record index_is_proper_limit {SI : indexT} (n : index) := mkproperlim {
  proper_limit_is_limit : index_is_limit n;
  proper_limit_not_zero : zero ≺ᵢ n;
}.
Global Arguments mkproperlim {_} _ _ _.
Global Arguments proper_limit_not_zero {_ _} _.
Global Arguments proper_limit_is_limit {_ _} _.

Record limit_idx {SI : indexT} := _mklimitidx {
  limit_index :> index;
  limit_index_is_proper :> index_is_proper_limit limit_index;
}.
Global Arguments _mklimitidx {_}.
Definition mklimitidx {SI : indexT} (n : index) Hlim Hz :=
  _mklimitidx n (mkproperlim n Hlim Hz).

Lemma limit_index_is_limit {SI : indexT} (n : limit_idx) : index_is_limit n.
Proof. apply limit_index_is_proper. Qed.
Lemma limit_index_not_zero {SI : indexT} (n : limit_idx) : zero ≺ᵢ n.
Proof. apply limit_index_is_proper. Qed.



(** ** Automation *)
(** The tactic [si_solver] solves goals that are solely concerned with
    step-indices and their relations (i.e., [zero], [succ n], [n ≺ᵢ m], and [n ⪯ᵢ m]).
    Currently, this tactic is just an alias for [lia]. However, in the future,
    Iris will generalize over the type of step-indices, and this tactic will
    be able to solve step-indexing goals also in this generalized setting.

    The tactic can be used as part of [eauto] by using the hint database
    [si_solver].
*)

Create HintDb si_solver.

Ltac si_solver := idtac.
Global Hint Extern 1 => si_solver : si_solver.

Tactic Notation "stepindex" "using" uconstr(H) := eauto using H with si_solver.
Tactic Notation "stepindex" := eauto with si_solver.

(** We derived properties for step-indices and their opertations. *)
Section step_index_properties.
  Context {SI : indexT}.
  Implicit Type (n m p : index).

  Global Instance: Inhabited index.
  Proof. constructor. exact zero. Qed.

  Global Instance index_le_refl : Reflexive (index_le).
  Proof.
    intros n. rewrite /index_le. eapply index_le_lt_iff. auto.
  Qed.

  Global Instance index_le_trans : Transitive (index_le).
  Proof.
    intros n m p. rewrite /index_le. rewrite !index_le_lt_iff.
    intros [Hnm|Hnm] [Hmp|Hmp]; subst; eauto using index_lt_trans.
  Qed.

  Global Instance index_lt_le_subrel : subrelation (index_lt) (index_le).
  Proof.
    intros n m H. rewrite /index_le. eapply index_le_lt_iff. auto.
  Qed.

  Global Instance: PreOrder (index_le).
  Proof.
    split; apply _.
  Qed.

  Lemma index_le_eq_or_lt (n m : index) : n ⪯ᵢ m → n = m ∨ n ≺ᵢ m.
  Proof. rewrite index_le_lt_iff; intros [|]; eauto. Qed.

  Lemma index_le_refl_auto (n m : index) (H : n = m) : n ⪯ᵢ m.
  Proof. rewrite H. apply index_le_refl. Qed.


  Local Hint Extern 1 (?a ⪯ᵢ ?a) => apply index_le_refl : si_solver.
  Local Hint Extern 2 (?a ⪯ᵢ ?b) => apply index_le_refl_auto : si_solver.
  Local Hint Extern 1 (?a ⪯ᵢ ?b) => apply index_lt_le_subrel : si_solver.

  Lemma index_le_total n m : {n ⪯ᵢ m} + {m ⪯ᵢ n}.
  Proof.
    destruct (index_lt_eq_lt_dec n m) as [[|]|]; stepindex.
  Qed.

  Lemma index_le_lt_dec n m : {n ⪯ᵢ m} + {m ≺ᵢ n}.
  Proof.
    edestruct (index_lt_eq_lt_dec n m) as [[H | H] | H]; stepindex.
  Defined.

  Lemma index_zero_minimum n : zero ⪯ᵢ n.
  Proof.
    destruct (index_le_total zero n) as [|Hle]; first by stepindex.
    eapply index_le_lt_iff in Hle as [Hlt|Heq]; subst; stepindex.
    exfalso; eapply (index_zero_least); stepindex.
  Qed.

  Lemma index_zero_is_unique n : (∀ m, ¬ (m ≺ᵢ n)) → n = zero.
  Proof.
    intros Hleast; destruct (index_le_total n zero)
      as [[]%index_le_eq_or_lt|[]%index_le_eq_or_lt]; stepindex; exfalso.
    - by eapply index_zero_least.
    - by eapply Hleast.
  Qed.

  Lemma index_is_zero n : {n = zero} + {zero ≺ᵢ n}.
  Proof.
    destruct (index_lt_eq_lt_dec n zero) as [[]|]; stepindex.
    exfalso; by eapply index_zero_least.
  Qed.

  Lemma index_lt_dec_minimum n : (∀ m, ¬ (m ≺ᵢ n)) + { m | m ≺ᵢ n}.
  Proof.
    destruct (index_lt_eq_lt_dec n zero) as [[]|].
    - exfalso; by eapply index_zero_least.
    - subst; left; exact index_zero_least.
    - right; by eexists.
  Qed.

  Lemma index_lt_irrefl n : ¬ (n ≺ᵢ n).
  Proof.
    induction n as [? IH] using (well_founded_ind (index_lt_wf)).
    intros H1; apply IH in H1 as ?; eauto.
  Qed.

  Lemma index_lt_le_trans n m p : n ≺ᵢ m → m ⪯ᵢ p → n ≺ᵢ p.
  Proof.
    rewrite index_le_lt_iff.
    intros ? []; subst; eauto.
    by transitivity m.
  Qed.

  Lemma index_le_lt_trans n m p : n ⪯ᵢ m → m ≺ᵢ p → n ≺ᵢ p.
  Proof. intros []%index_le_eq_or_lt ?; subst; eauto. by transitivity m. Qed.

  Lemma index_le_lt_contradict n n' : n ⪯ᵢ n' → n' ≺ᵢ n → False.
  Proof.
    intros H1 H2. enough (n ≺ᵢ n) by (by eapply index_lt_irrefl).
    by eapply index_le_lt_trans.
  Qed.

  Lemma index_lt_le_contradict n n' : n ≺ᵢ n' → n' ⪯ᵢ n → False.
  Proof.
    intros H1 H2. enough (n ≺ᵢ n) by (by eapply index_lt_irrefl).
    by eapply index_lt_le_trans.
  Qed.

  Lemma index_le_ge_eq n n' : n ⪯ᵢ n' → n' ⪯ᵢ n → n = n'.
  Proof.
    intros [-> | H1]%index_le_eq_or_lt [H2 | H2]%index_le_eq_or_lt; try by eauto.
    exfalso; eapply index_lt_irrefl. by eapply index_lt_trans.
  Qed.

  Lemma index_succ_iff n m : n ⪯ᵢ m ↔ n ≺ᵢ succ m.
  Proof.
    split.
    - intros Hle%index_le_eq_or_lt.
      destruct Hle; subst; last transitivity m.
      all: eauto; eapply index_succ_greater.
    - destruct (index_le_total n m) as [|[|H1]%index_le_eq_or_lt]; [by stepindex..|].
      apply index_succ_least in H1. intros Hlt.
      eapply index_lt_le_trans in H1; stepindex.
      exfalso; eapply index_lt_irrefl; eauto.
  Qed.

  Lemma index_le_lt_eq_dec n m : n ⪯ᵢ m → {n ≺ᵢ m} + {n = m}.
  Proof.
    intros Hle. destruct (index_lt_eq_lt_dec n m) as [[H | H] | H].
    - by left.
    - by right.
    - exfalso. eapply index_lt_irrefl with (n := n). by eapply index_le_lt_trans.
  Qed.

  Lemma index_lt_succ_mono n m : n ≺ᵢ m → succ n ≺ᵢ succ m.
  Proof.
    intros. by eapply index_succ_iff, index_succ_least.
  Qed.

  Lemma index_le_succ_mono n m : n ⪯ᵢ m → succ n ⪯ᵢ succ m.
  Proof.
    intros [->|H % index_lt_succ_mono]%index_le_eq_or_lt; stepindex.
  Qed.

  Lemma index_succ_greater' n m : n = succ m → m ≺ᵢ n.
  Proof. intros ->; by apply index_succ_greater. Qed.

  Lemma index_succ_neq n : n ≠ succ n.
  Proof.
    intros H%index_succ_greater'. by eapply index_lt_irrefl.
  Qed.

  Lemma index_lt_succ_inj n m : succ n ≺ᵢ succ m → n ≺ᵢ m.
  Proof.
    destruct (index_le_total n m) as [[]%index_le_eq_or_lt|H].
    - subst; intros [] % index_lt_irrefl.
    - auto.
    - intros H'. apply index_le_succ_mono in H.
      specialize (index_le_lt_trans _ _ _ H H') as [] % index_lt_irrefl.
  Qed.

  Lemma index_succ_inj n m : succ n = succ m → n = m.
  Proof.
    intros H. destruct (index_lt_eq_lt_dec n m) as [[H'|]|H']; eauto; exfalso.
    all: eapply index_lt_succ_mono in H'; rewrite H in H'; by eapply index_lt_irrefl.
  Qed.

  Lemma index_le_succ_inj n m : succ n ⪯ᵢ succ m → n ⪯ᵢ m.
  Proof.
    intros [Heq | Hlt]%index_le_eq_or_lt.
    - apply index_succ_inj in Heq. stepindex.
    - apply index_lt_succ_inj in Hlt. stepindex.
  Qed.

  Lemma index_eq_dec n m : {n = m} + {n ≠ m}.
  Proof.
    destruct (index_lt_eq_lt_dec n m) as [[H|H]|H]; subst.
    - right; intros ->; by eapply index_lt_irrefl.
    - by left.
    - right; intros ->; by eapply index_lt_irrefl.
  Qed.

  Lemma index_succ_le_lt n m : succ n ⪯ᵢ m ↔ n ≺ᵢ m.
  Proof.
    split.
    - intros [<- | H1]%index_le_eq_or_lt; [eapply index_succ_greater | ].
      eapply index_lt_trans; [ eapply index_succ_greater | eauto ].
    - intros H. destruct (index_lt_eq_lt_dec (succ n) m) as [[Hlt | Heq] | Hgt].
      + stepindex.
      + stepindex.
      + exfalso. eapply index_succ_least in Hgt.
        apply index_le_succ_inj in Hgt.
        eapply index_lt_irrefl. by eapply index_lt_le_trans.
  Qed.

  Lemma index_succ_le n m : succ n ⪯ᵢ m → n ⪯ᵢ m.
  Proof.
    intros ?. eapply index_le_lt_iff.
    left. by apply index_succ_le_lt.
  Qed.

  Lemma index_lt_succ_tight n m : n ≺ᵢ m → m ≺ᵢ succ n → False.
  Proof.
    intros H1%index_succ_le_lt H2. eapply index_lt_irrefl, index_le_lt_trans; eauto.
  Qed.

  Lemma index_succ_not_zero n : succ n ≠ zero.
  Proof.
    intros H. eapply index_zero_least, index_succ_greater'. by symmetry.
  Qed.

  Lemma index_succ_not_limit m : ¬ (∀ n, n ≺ᵢ succ m → succ n ≺ᵢ succ m).
  Proof.
    intros H. eapply index_lt_irrefl, H. apply index_succ_greater.
  Qed.

  Lemma index_limit_not_succ m : index_is_limit m → ∀ n, m ≠ succ n.
  Proof.
    intros H n Hn. specialize (H n). rewrite Hn in H.
    eapply index_lt_irrefl. apply H, index_succ_greater.
  Qed.

End step_index_properties.

Global Hint Immediate index_zero_minimum : si_solver.
Global Hint Resolve index_succ_greater : si_solver.
Global Hint Resolve <- index_succ_iff : si_solver.

Global Hint Extern 1 (?a ⪯ᵢ ?a) => apply index_le_refl : si_solver.
Global Hint Extern 2 (?a ⪯ᵢ ?b) => apply index_le_refl_auto : si_solver.
Global Hint Extern 1 (?a ⪯ᵢ ?b) => apply index_lt_le_subrel : si_solver.

Global Hint Extern 1 False => eapply index_lt_irrefl : si_solver.
Global Hint Resolve -> index_succ_iff : si_solver.
Global Hint Resolve index_succ_greater : si_solver.
Global Hint Resolve index_le_succ_inj : si_solver.
Global Hint Resolve index_lt_succ_mono : si_solver.
Global Hint Immediate index_zero_minimum : si_solver.


(** Ordinal recursion

  We define two recursion schemes for ordinal induction (i.e., transfinite
  induction), [index_rec] and [index_cumulative_rec].
  The first one, [index_rec], is the standard induction priciciple:
    P zero →
    (∀ i, P i → P (succ i)) →
    (∀ i: limit_idx, (∀ j, j ≺ᵢ i → P j) → P i) →
    ∀ i, P i

  The second one, [index_cumulative_rec], can be used to define a family of
  values [f] by recursion on a step-index [i]. That is, it returns
    ∀ i: index, {f: ∀ j ≺ i, P j | Q i f}
  such that the entire family satisfies a property [Q] (e.g., some compatibility
  property between the elements of the family). We use this recursor to define
  the step-indexed [fixpoint] of Iris (see ofe.v).
*)
Section ordinal_recursor.
  Context {SI : indexT}.

  (** Standard ordinal recursion with the right computational behavior. *)
  Definition index_rec (P: index → Type) : P zero → (∀ n, P n → P (succ n)) → (∀ n: limit_idx, (∀ m, m ≺ᵢ n → P m) → P n) → ∀ n, P n :=
    λ s f lim, Fix (index_lt_wf) _ (λ n IH,
        match index_is_zero n with
        | left EQ => eq_rect_r P s EQ
        | right NZ =>
          match index_dec_limit n with
          | inl (exist _ m EQ) => eq_rect_r P (f m (IH m (index_succ_greater' n m EQ))) EQ
          | inr Hlim => lim (mklimitidx n Hlim NZ) IH
          end
        end
      ).

  Lemma index_type_dec (n : index) :
    (n = zero) + { n' | n = succ n'} + (index_is_limit n).
  Proof.
    revert n. apply index_rec.
    - by left; left.
    - intros n _; left; right. by exists n.
    - intros n _. right. apply limit_index_is_limit.
  Defined.

  Class index_rec_lim_ext {P : index → Type} (lim : ∀ n : limit_idx, (∀ m, m ≺ᵢ n → P m) → P n) := {
    index_rec_lim_ext_proofs n H1 H2 f : lim n f = lim (mklimitidx n H2 H1) f;
    index_rec_lim_ext_function n f g : (∀ m Hm, f m Hm = g m Hm) → lim n f = lim n g
  }.

  Lemma index_rec_unfold P s f lim `{index_rec_lim_ext P lim} n :
    index_rec P s f lim n =
    match index_is_zero n with
    | left EQ => eq_rect_r P s EQ
    | right NZ =>
      match index_dec_limit n with
      | inl (exist _ m EQ) => eq_rect_r P (f m (index_rec P s f lim m)) EQ
      | inr Hlim => lim (mklimitidx n Hlim NZ) (λ m _, index_rec P s f lim m)
      end
    end.
  Proof.
    unfold index_rec at 1. rewrite Fix_eq.
    - reflexivity.
    - intros m g h EQ. destruct index_is_zero; first done.
      destruct index_dec_limit as [[p EQ']|].
      + by rewrite EQ.
      + erewrite index_rec_lim_ext_function; done.
  Qed.


  Lemma index_rec_zero P s f lim `{index_rec_lim_ext P lim} :
    index_rec P s f lim zero = s.
  Proof.
    rewrite index_rec_unfold.
    destruct index_is_zero as [EQ|NT].
    - symmetry. apply Eqdep_dec.eq_rect_eq_dec, index_eq_dec.
    - exfalso; by eapply index_lt_irrefl.
  Qed.

  Lemma index_rec_succ P s f lim `{index_rec_lim_ext P lim} n :
    index_rec P s f lim (succ n) = f n (index_rec P s f lim n).
  Proof.
    rewrite index_rec_unfold.
    destruct index_is_zero as [EQ|NT];[|destruct index_dec_limit as [[m EQ]|Hlim]].
    - exfalso. by eapply index_succ_not_zero.
    - eapply index_succ_inj in EQ as EQ'. subst n.
      symmetry. apply Eqdep_dec.eq_rect_eq_dec, index_eq_dec.
    - exfalso. eapply index_lt_irrefl, Hlim, index_succ_greater.
  Qed.

  Lemma index_rec_lim P s f lim `{index_rec_lim_ext P lim} (n : limit_idx):
    index_rec P s f lim n = lim n (λ m _, index_rec P s f lim m).
  Proof.
    rewrite index_rec_unfold.
    destruct index_is_zero as [EQ|NT];[|destruct index_dec_limit as [[m EQ]|Hlim]].
    - exfalso. specialize (limit_index_not_zero n). rewrite EQ. by apply index_lt_irrefl.
    - exfalso. specialize (limit_index_is_limit n m (index_succ_greater' _ _ EQ)).
      rewrite EQ. by apply index_lt_irrefl.
    - simpl. symmetry. apply index_rec_lim_ext_proofs.
  Qed.
End ordinal_recursor.

Section ordinal_cumulative_recursor.
  Context {SI : indexT}.
  Variable (P : index → Type) (Q : ∀ n, (∀ m, m ≺ᵢ n → P m) → Type).

  Let R n := {f : ∀ m, m ≺ᵢ n → P m & Q n f}.

  (** Cummulative Ordinal Recursor *)
  Lemma index_cumulative_rec (F : ∀ n, R n → P n):
    (∀ n G, Q n (λ m Hm, F m (G m Hm))) → (∀ n, R n).
  Proof.
    intros IH. apply (Fix (index_lt_wf)).
    intros n G. unfold R. unshelve econstructor.
    - intros m Hm. by eapply F, G.
    - by apply IH.
  Defined.

  Lemma index_cumulative_rec_dep (F : ∀ n, R n → P n):
    (∀ n G, Q n (λ m Hm, F m (G m Hm))) → (∀ n (H : Acc (≺ᵢ) n), R n).
  Proof.
    intros IH. apply (Fix_F).
    intros n G. unfold R. unshelve econstructor.
    - intros m Hm. by eapply F, G.
    - by apply IH.
  Defined.

  Lemma index_cumulative_rec_dep_step F step m succs :
    index_cumulative_rec_dep F step m (Acc_intro m succs) =
    existT (λ p Hp, F p (index_cumulative_rec_dep F step p (succs p Hp)))
      (step m (λ p Hp, index_cumulative_rec_dep F step p (succs p Hp))).
  Proof. reflexivity. Qed.

  Lemma index_cumulative_rec_unfold F step (M : ∀ n, R n → Prop) :
    (∀ m succs, (∀ p (Hp : p ≺ᵢ m), M p (index_cumulative_rec_dep F step p (succs p Hp))) → M m (index_cumulative_rec_dep F step m (Acc_intro m succs)))
    → ∀ m, M m (index_cumulative_rec F step m).
  Proof.
    intros H m. unfold index_cumulative_rec, Fix.
    pattern m, (index_lt_wf m). eapply Acc_inv_dep. clear m.
    intros m succs Hm.
    unfold index_cumulative_rec_dep in H.
    eapply H. apply Hm.
  Qed.
  Global Opaque index_cumulative_rec_dep.
  Global Opaque index_cumulative_rec.
End ordinal_cumulative_recursor.

(** Finite indices are exactly the natural numbers *)
Class FiniteIndex (SI : indexT) :=
  finite_index (n : index) : n = zero ∨ ∃ m, n = succ m.
