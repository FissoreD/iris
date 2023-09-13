From iris.algebra Require Import auth excl lib.gmap_view lib.frac_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.

Section test_dist_equiv_mode.
  (* check that the mode for [Dist] does not trigger https://github.com/coq/coq/issues/14441.
  From https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/700#note_69303. *)
  Lemma list_dist_lookup {A : ofe} n (l1 l2 : list A) :
    l1 ≡{n}≡ l2 ↔ ∀ i, l1 !! i ≡{n}≡ l2 !! i.
  Abort.

  (* analogous test for [Equiv] and https://github.com/coq/coq/issues/14441.
  From https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/700#note_69303. *)
  Lemma list_equiv_lookup_ofe {A : ofe} (l1 l2 : list A) :
    l1 ≡ l2 ↔ ∀ i, l1 !! i ≡ l2 !! i.
  Abort.
End test_dist_equiv_mode.

(** Make sure that the same [Equivalence] instance is picked for Leibniz OFEs
with carriers that are definitionally equal. See also
https://gitlab.mpi-sws.org/iris/iris/issues/299 *)
Definition tag := nat.
Canonical Structure tagO := leibnizO tag.
Goal tagO = natO.
Proof. reflexivity. Qed.

Global Instance test_cofe {Σ} : Cofe (iPrePropO Σ) := _.

Section tests.
  Context `{!invGS_gen hlc Σ}.

  Program Definition test : (iPropO Σ -n> iPropO Σ) -n> (iPropO Σ -n> iPropO Σ) :=
    λne P v, (▷ (P v))%I.
  Solve Obligations with solve_proper.

End tests.

(** Check that [@Reflexive Prop ?r] picks the instance setoid_rewrite needs.
    Really, we want to set [Hint Mode Reflexive] in a way that this fails, but
    we cannot [1].  So at least we try to make sure the first solution found
    is the right one, to not pay performance in the success case [2].

    [1] https://github.com/coq/coq/issues/7916
    [2] https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp/merge_requests/38
*)
Lemma test_setoid_rewrite :
  ∃ R, @Reflexive Prop R ∧ R = iff.
Proof.
  eexists. split.
  - apply _.
  - reflexivity.
Qed.

(** Minimal example of an inference that worked when the [ofe]/[cmra]/[ucmra]
   hierarchy was fully bundled. The tricky part here is the interaction between
   the three structures: the [equiv] instance comes from [ofe], the [op] from
   [cmra], but the proof comes from [ucmra]. The type of the goal infers the
   largest superclass (i.e., [ofe]),  while we need the smallest. Apparently,
   the _old_ unification from [simple eapply] might choke in this, while we
   need to make typeclass search work. To debug this, the
     Set Debug "all".
   command is helpful. *)

Lemma test_prodUR_inference1 {A : ucmra} : LeftId equiv ε (@op (prod A A) _).
Proof. apply _. Qed.

Lemma test_prodUR_inference2 {A : ucmra} : LeftId equiv ε (@op (prod A unit) _).
Proof. apply _. Qed.

Lemma test_prodUR_inference3 {A : ucmra} : LeftId equiv (ε, ε) (@op (prod A unit) _).
Proof. apply _. Qed.

(** Regression test for <https://gitlab.mpi-sws.org/iris/iris/issues/255>. *)
Definition testR := authR (prodUR
        (prodUR
          (optionUR (exclR unitO))
          (optionUR (exclR unitO)))
        (optionUR (agreeR (boolO)))).
Section test_prod.
  Context `{!inG Σ testR}.
  Lemma test_prod_persistent γ :
    Persistent (PROP:=iPropI Σ) (own γ (◯((None, None), Some (to_agree true)))).
  Proof. apply _. Qed.
End test_prod.

(** Make sure the [auth]/[gmap_view] notation does not mix up its arguments. *)
Definition auth_check {A : ucmra} :
  auth A = authO A := eq_refl.
Definition gmap_view_check {K : Type} `{Countable K} {V : ofe} :
  gmap_view K V = gmap_viewO K V := eq_refl.

(** Make sure one can freely use [ucmra] combinators where [cmra] combinators
    were needed, i.e. [frac_authUR] where [frac_authR] would suffice. See also
    https://gitlab.mpi-sws.org/iris/iris/-/issues/539
*)
Timeout 1 Lemma stack_frac_authsUR7
  `{!inG Σ (frac_authUR $ frac_authUR $ frac_authUR $ frac_authUR $
            frac_authUR $ frac_authUR $ frac_authUR $ agreeR $ natO)} γ :
      own γ (●F (●F (●F (●F (●F (●F (●F (to_agree O)))))))) ⊢
      own γ (●F (●F (●F (●F (●F (●F (●F (to_agree O)))))))).
Proof. Timeout 1 reflexivity. Timeout 1 Qed.

Definition frac_auth A := (auth (optionR $ prodR fracR A)).
(** Make sure it is also okay to use the [_ : cmra → Type] combinators,
    and letting Coq do the inference. See also
    https://gitlab.mpi-sws.org/iris/iris/-/issues/539
*)
Timeout 1 Lemma stack_frac_auths7
  `{!inG Σ (frac_auth $ frac_auth $ frac_auth $ frac_auth $
            frac_auth $ frac_auth $ frac_auth $ agree $ nat)} γ :
      own γ (●F (●F (●F (●F (●F (●F (●F (to_agree O)))))))) ⊢
      own γ (●F (●F (●F (●F (●F (●F (●F (to_agree O)))))))).
Proof. Timeout 1 reflexivity. Timeout 1 Qed.

(** Make sure that stacking the authoritative cmra combinator does not blow up
    type checking time. See also
    https://gitlab.mpi-sws.org/iris/iris/-/issues/539
*)
Timeout 1 Lemma stack_auths_unit_okay :
  (● (● (● (● (● (● (● (● (● (● (● (● (()))))))))))))) =
  (● (● (● (● (● (● (● (● (● (● (● (● (()))))))))))))).
Proof. Timeout 1 reflexivity. Timeout 1 Qed.

(** Testing conversion speed for some large [cmra]s *)
Section hw_gpfsl_cmra.
  (* This cmra is found in [proof_hw_graph] in [gpfsl]. *)
  Definition large_cmra1_R := (
      prodR
        (prodR (prodR (optionR (agreeR (leibnizO gname))) (authR max_natUR))
               (authR
              (gmapUR nat
                 (prodR
                    (prodR
                       (prodR (optionR (agreeR (leibnizO (Z * nat))))
                          (optionR (csumR (exclR unitR) (agreeR (leibnizO (nat * nat))))))
                       (optionR (agreeR (leibnizO nat)))) (optionR (agreeR (leibnizO gname)))))))
        (authR (gmapUR nat (agreeR (leibnizO nat))))).

  Definition large_cmra1_UR := (
      prodUR
        (prodUR (prodUR (optionUR (agreeR (leibnizO gname))) (authUR max_natUR))
           (authUR
              (gmapUR nat
                 (prodUR
                    (prodUR
                       (prodUR (optionUR (agreeR (leibnizO (Z * nat))))
                          (optionUR (csumR (exclR unitR) (agreeR (leibnizO (nat * nat))))))
                       (optionUR (agreeR (leibnizO nat)))) (optionUR (agreeR (leibnizO gname)))))))
        (authUR (gmapUR nat (agreeR (leibnizO nat))))).

  Definition large_cmra1_el : large_cmra1_UR := ε.

  Timeout 1 Lemma test_large_cmra1_conversion : large_cmra1_el = (large_cmra1_el : large_cmra1_R).
  Proof. Timeout 1 reflexivity. Timeout 1 Qed.


  Definition large_cmra2_R := (
    gmapR nat $ gmapR nat $ gmapR nat $ gmapR nat $ gmapR nat $ gmapR nat $
    agreeR nat).

  Definition large_cmra2_UR := (
    gmapUR nat $ gmapUR nat $ gmapUR nat $ gmapUR nat $ gmapUR nat $ gmapUR nat $
    agreeR nat).

  Definition large_cmra2_el : large_cmra2_UR := ε.

  Timeout 1 Lemma test_large_cmra2_conversion : large_cmra2_el = (large_cmra2_el : large_cmra2_R).
  Proof. Timeout 1 reflexivity. Timeout 1 Qed.


  Definition large_cmra3_R := (
    optionR $ optionR $ optionR $ optionR $ optionR $ optionR $ optionR $
    agreeR nat).

  Definition large_cmra3_UR := (
    optionUR $ optionUR $ optionUR $ optionUR $ optionUR $ optionUR $ optionUR $
    agreeR nat).

  Definition large_cmra3_el : large_cmra3_UR := ε.

  Timeout 1 Lemma test_large_cmra3_conversion : large_cmra3_el = (large_cmra3_el : large_cmra3_R).
  Proof. Timeout 1 reflexivity. Timeout 1 Qed.
End hw_gpfsl_cmra.


Lemma uncurry_ne_test {A B C : ofe} (f : A → B → C) :
  NonExpansive2 f → NonExpansive (uncurry f).
Proof. apply _. Qed.
Lemma uncurry3_ne_test {A B C D : ofe} (f : A → B → C → D) :
  NonExpansive3 f → NonExpansive (uncurry3 f).
Proof. apply _. Qed.
Lemma uncurry4_ne_test {A B C D E : ofe} (f : A → B → C → D → E) :
  NonExpansive4 f → NonExpansive (uncurry4 f).
Proof. apply _. Qed.

Lemma curry_ne_test {A B C : ofe} (f : A * B → C) :
  NonExpansive f → NonExpansive2 (curry f).
Proof. apply _. Qed.
Lemma curry3_ne_test {A B C D : ofe} (f : A * B * C → D) :
  NonExpansive f → NonExpansive3 (curry3 f).
Proof. apply _. Qed.
Lemma curry4_ne_test {A B C D E : ofe} (f : A * B * C * D → E) :
  NonExpansive f → NonExpansive4 (curry4 f).
Proof. apply _. Qed.
