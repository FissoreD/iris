Require Import world_prop core_lang masks.
Require Import ModuRes.RA ModuRes.UPred ModuRes.BI ModuRes.PreoMet ModuRes.Finmap.

Module IrisRes (RL : RA_T) (C : CORE_LANG) <: RA_T.
  Instance state_type : Setoid C.state := discreteType.
  
  Definition res := (ra_res_ex C.state * RL.res)%type.
  Instance res_type : Setoid res := _.
  Instance res_op   : RA_op res := _.
  Instance res_unit : RA_unit res := _.
  Instance res_valid: RA_valid res := _.
  Instance res_ra   : RA res := _.

  (* The order on (ra_pos res) is inferred correctly, but this one is not *)
  Instance res_pord: preoType res := ra_preo res.
End IrisRes.

Module IrisCore (RL : RA_T) (C : CORE_LANG).
  Export C.
  Module Export R  := IrisRes RL C.
  Module Export WP := WorldProp R.

  Delimit Scope iris_scope with iris.
  Local Open Scope iris_scope.

  (** Instances for a bunch of types (some don't even have Setoids) *)
  Instance state_metr : metric state := discreteMetric.
  Instance state_cmetr : cmetric state := discreteCMetric.

  Instance logR_metr : metric RL.res := discreteMetric.
  Instance logR_cmetr : cmetric RL.res := discreteCMetric.

  Instance nat_type : Setoid nat := discreteType.
  Instance nat_metr : metric nat := discreteMetric.
  Instance nat_cmetr : cmetric nat := discreteCMetric.

  Instance expr_type : Setoid expr := discreteType.
  Instance expr_metr : metric expr := discreteMetric.
  Instance expr_cmetr : cmetric expr := discreteCMetric.

  (* We use this type quite a bit, so give it and its instances names *)
  Definition vPred := value -n> Props.
  Instance vPred_type  : Setoid vPred  := _.
  Instance vPred_metr  : metric vPred  := _.
  Instance vPred_cmetr : cmetric vPred := _.


  (** The final thing we'd like to check is that the space of
      propositions does indeed form a complete BI algebra.

      The following instance declaration checks that an instance of
      the complete BI class can be found for Props (and binds it with
      a low priority to potentially speed up the proof search).
   *)

  Instance Props_BI : ComplBI Props | 0 := _.
  Instance Props_Later : Later Props | 0 := _.
  
  (** And now we're ready to build the IRIS-specific connectives! *)

  Section Necessitation.
    (** Note: this could be moved to BI, since it's possible to define
        for any UPred over a monoid. **)

    Local Obligation Tactic := intros; resp_set || eauto with typeclass_instances.

    Program Definition box : Props -n> Props :=
      n[(fun p => m[(fun w => mkUPred (fun n r => p w n ra_pos_unit) _)])].
    Next Obligation.
      intros n m r s HLe _ Hp; rewrite HLe; assumption.
    Qed.
    Next Obligation.
      intros w1 w2 EQw m r HLt; simpl.
      eapply (met_morph_nonexp _ _ p); eassumption.
    Qed.
    Next Obligation.
      intros w1 w2 Subw n r; simpl.
      apply p; assumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w m r HLt; simpl.
      apply EQp; assumption.
    Qed.

  End Necessitation.

  (** "Internal" equality **)
  Section IntEq.
    Context {T} `{mT : metric T}.

    Program Definition intEqP (t1 t2 : T) : UPred pres :=
      mkUPred (fun n r => t1 = S n = t2) _.
    Next Obligation.
      intros n1 n2 _ _ HLe _; apply mono_dist; now auto with arith.
    Qed.

    Definition intEq (t1 t2 : T) : Props := pcmconst (intEqP t1 t2).

    Instance intEq_equiv : Proper (equiv ==> equiv ==> equiv) intEqP.
    Proof.
      intros l1 l2 EQl r1 r2 EQr n r.
      split; intros HEq; do 2 red.
      - rewrite <- EQl, <- EQr; assumption.
      - rewrite EQl, EQr; assumption.
    Qed.

    Instance intEq_dist n : Proper (dist n ==> dist n ==> dist n) intEqP.
    Proof.
      intros l1 l2 EQl r1 r2 EQr m r HLt.
      split; intros HEq; do 2 red.
      - etransitivity; [| etransitivity; [apply HEq |] ];
        apply mono_dist with n; eassumption || now auto with arith.
      - etransitivity; [| etransitivity; [apply HEq |] ];
        apply mono_dist with n; eassumption || now auto with arith.
    Qed.

  End IntEq.

  Notation "t1 '===' t2" := (intEq t1 t2) (at level 70) : iris_scope.

  Section Invariants.

    (** Invariants **)
    Definition invP (i : nat) (p : Props) (w : Wld) : UPred pres :=
      intEqP (w i) (Some (ı' p)).
    Program Definition inv i : Props -n> Props :=
      n[(fun p => m[(invP i p)])].
    Next Obligation.
      intros w1 w2 EQw; unfold invP; simpl morph.
      destruct n; [apply dist_bound |].
      apply intEq_dist; [apply EQw | reflexivity].
    Qed.
    Next Obligation.
      intros w1 w2 Sw; unfold invP; simpl morph.
      intros n r HP; do 2 red; specialize (Sw i); do 2 red in HP.
      destruct (w1 i) as [μ1 |]; [| contradiction].
      destruct (w2 i) as [μ2 |]; [| contradiction]; simpl in Sw.
      rewrite <- Sw; assumption.
    Qed.
    Next Obligation.
      intros p1 p2 EQp w; unfold invP; simpl morph.
      apply intEq_dist; [reflexivity |].
      apply dist_mono, (met_morph_nonexp _ _ ı'), EQp.
    Qed.

  End Invariants.

  Notation "□ p" := (box p) (at level 30, right associativity) : iris_scope.
  Notation "⊤" := (top : Props) : iris_scope.
  Notation "⊥" := (bot : Props) : iris_scope.
  Notation "p ∧ q" := (and p q : Props) (at level 40, left associativity) : iris_scope.
  Notation "p ∨ q" := (or p q : Props) (at level 50, left associativity) : iris_scope.
  Notation "p * q" := (sc p q : Props) (at level 40, left associativity) : iris_scope.
  Notation "p → q" := (BI.impl p q : Props) (at level 55, right associativity) : iris_scope.
  Notation "p '-*' q" := (si p q : Props) (at level 55, right associativity) : iris_scope.
  Notation "∀ x , p" := (all n[(fun x => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.
  Notation "∃ x , p" := (xist n[(fun x => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.
  Notation "∀ x : T , p" := (all n[(fun x : T => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.
  Notation "∃ x : T , p" := (xist n[(fun x : T => p)] : Props) (at level 60, x ident, no associativity) : iris_scope.

  Lemma valid_iff p :
    valid p <-> (⊤ ⊑ p).
  Proof.
    split; intros Hp.
    - intros w n r _; apply Hp.
    - intros w n r; apply Hp; exact I.
  Qed.

  Section Ownership.
    Local Open Scope ra.

    (** Ownership **)
    (* We define this on *any* resource, not just the positive (valid) ones.
       Note that this makes ownR trivially *False* for invalid u: There is no
       elment v such that u · v = r (where r is valid) *)
    Program Definition ownR: res -=> Props :=
      s[(fun u => pcmconst (mkUPred(fun n r => u ⊑ ra_proj r) _) )].
    Next Obligation.
      intros n m r1 r2 Hle [d Hd ] [e He]. change (u ⊑ (ra_proj r2)). rewrite <-Hd, <-He.
      exists (d · e). rewrite assoc. reflexivity.
    Qed.
    Next Obligation.
      intros u1 u2 Hequ. intros w n r. split; intros [t Heqt]; exists t; [rewrite <-Hequ|rewrite Hequ]; assumption.
    Qed.

    Lemma ownR_sc u t:
      ownR (u · t) == ownR u * ownR t.
    Proof.
      intros w n r; split; [intros Hut | intros [r1 [r2 [EQr [Hu Ht] ] ] ] ].
      - destruct Hut as [s Heq]. rewrite assoc in Heq.
        exists✓ (s · u) by auto_valid.
        exists✓ t by auto_valid.
        split; [|split].
        + rewrite <-Heq. reflexivity.
        + exists s. reflexivity.
        + do 13 red. reflexivity.
      - destruct Hu as [u' Hequ]. destruct Ht as [t' Heqt].
        exists (u' · t'). rewrite <-EQr, <-Hequ, <-Heqt.
        rewrite !assoc. eapply ra_op_proper; try (reflexivity || now apply _).
        rewrite <-assoc, (comm _ u), assoc. reflexivity.
    Qed.

    Lemma ownR_valid u (INVAL: ~✓u):
      ownR u ⊑ ⊥.
    Proof.
      intros w n [r VAL] [v Heq]. hnf. unfold ra_proj, proj1_sig in Heq.
      rewrite <-Heq in VAL. apply ra_op_valid2 in VAL. contradiction.
    Qed.

    (** Proper physical state: ownership of the machine state **)
    Program Definition ownS : state -n> Props :=
      n[(fun s => ownR (ex_own _ s, 1%ra))].
    Next Obligation.
      intros r1 r2 EQr; destruct n as [| n]; [apply dist_bound |].
      rewrite EQr. reflexivity.
    Qed.

    (** Proper ghost state: ownership of logical **)
    Program Definition ownL : RL.res -n> Props :=
      n[(fun r => ownR (ex_unit _, r))].
    Next Obligation.
      intros r1 r2 EQr. destruct n as [| n]; [apply dist_bound |eapply dist_refl].
      simpl in EQr. intros w m t. simpl. change ( (ex_unit state, r1) ⊑ (ra_proj t) <->  (ex_unit state, r2) ⊑ (ra_proj t)). rewrite EQr. reflexivity.
    Qed.

    (** Ghost state ownership **)
    Lemma ownL_sc (u t : RL.res) :
      ownL (u · t) == ownL u * ownL t.
    Proof.
      assert (Heq: (ex_unit state, u · t) == ((ex_unit state, u) · (ex_unit state, t)) ) by reflexivity.
      (* I cannot believe I have to write this... *)
      change (ownR (ex_unit state, u · t) == ownR (ex_unit state, u) * ownR (ex_unit state, t)).
      rewrite Heq.
      now eapply ownR_sc.
    Qed.

  End Ownership.

  (** Lemmas about box **)
  Lemma box_intro p q (Hpq : □ p ⊑ q) :
    □ p ⊑ □ q.
  Proof.
    intros w n r Hp; simpl; apply Hpq, Hp.
  Qed.

  Lemma box_elim p :
    □ p ⊑ p.
  Proof.
    intros w n r Hp; simpl in Hp.
    eapply uni_pred, Hp; [reflexivity |].
    now eapply unit_min.
  Qed.

  Lemma box_top : ⊤ == □ ⊤.
  Proof.
    intros w n r; simpl; unfold const; reflexivity.
  Qed.

  Lemma box_disj p q :
    □ (p ∨ q) == □ p ∨ □ q.
  Proof.
    intros w n r; reflexivity.
  Qed.

  (** Timeless *)

  Definition timelessP (p : Props) w n :=
    forall w' k r (HSw : w ⊑ w') (HLt : k < n) (Hp : p w' k r), p w' (S k) r.

  Program Definition timeless (p : Props) : Props :=
    m[(fun w => mkUPred (fun n r => timelessP p w n) _)].
  Next Obligation.
    intros n1 n2 _ _ HLe _ HT w' k r HSw HLt Hp; eapply HT, Hp; [eassumption |].
    now eauto with arith.
  Qed.
  Next Obligation.
    intros w1 w2 EQw k; simpl; intros _ HLt; destruct n as [| n]; [now inversion HLt |].
    split; intros HT w' m r HSw HLt' Hp.
    - symmetry in EQw; assert (HD := extend_dist _ _ _ _ EQw HSw); assert (HS := extend_sub _ _ _ _ EQw HSw).
      apply (met_morph_nonexp _ _ p) in HD; apply HD, HT, HD, Hp; now (assumption || eauto with arith).
    - assert (HD := extend_dist _ _ _ _ EQw HSw); assert (HS := extend_sub _ _ _ _ EQw HSw).
      apply (met_morph_nonexp _ _ p) in HD; apply HD, HT, HD, Hp; now (assumption || eauto with arith).
  Qed.
  Next Obligation.
    intros w1 w2 HSw n; simpl; intros _ HT w' m r HSw' HLt Hp.
    eapply HT, Hp; [etransitivity |]; eassumption.
  Qed.

  Section WorldSatisfaction.
    Local Open Scope ra_scope.
    Local Open Scope bi_scope.

    (* First, we need to compose the resources of a finite map. This won't be pretty, for
       now, since the library does not provide enough
       constructs. Hopefully we can provide a fold that'd work for
       that at some point
     *)
    Fixpoint comp_list (xs : list pres) : res :=
      match xs with
        | nil => 1
        | (x :: xs)%list => ra_proj x · comp_list xs
      end.

    Lemma comp_list_app rs1 rs2 :
      comp_list (rs1 ++ rs2) == comp_list rs1 · comp_list rs2.
    Proof.
      induction rs1; simpl comp_list; [now rewrite ra_op_unit by apply _ |].
      now rewrite IHrs1, assoc.
    Qed.

    Definition cod (m : nat -f> pres) : list pres := List.map snd (findom_t m).
    Definition comp_map (m : nat -f> pres) : res := comp_list (cod m).

    Lemma comp_map_remove (rs : nat -f> pres) i r (HLu : rs i = Some r) :
      comp_map rs == ra_proj r · comp_map (fdRemove i rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [discriminate |]; simpl comp_list; simpl in HLu.
      destruct (comp i j); [inversion HLu; reflexivity | discriminate |].
      simpl comp_list; rewrite IHrs by eauto using SS_tail.
      rewrite !assoc, (comm (_ s)); reflexivity.
    Qed.

    Lemma comp_map_insert_new (rs : nat -f> pres) i r (HNLu : rs i = None) :
      ra_proj r · comp_map rs == comp_map (fdUpdate i r rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [reflexivity | simpl comp_list; simpl in HNLu].
      destruct (comp i j); [discriminate | reflexivity |].
      simpl comp_list; rewrite <- IHrs by eauto using SS_tail.
      rewrite !assoc, (comm (_ r)); reflexivity.
    Qed.

    Lemma comp_map_insert_old (rs : nat -f> pres) i r1 r2 r
          (HLu : rs i = Some r1) (HEq : ra_proj r1 · ra_proj r2 == ra_proj r) :
      ra_proj r2 · comp_map rs == comp_map (fdUpdate i r rs).
    Proof.
      destruct rs as [rs rsP]; unfold comp_map, cod, findom_f in *; simpl findom_t in *.
      induction rs as [| [j s] ]; [discriminate |]; simpl comp_list; simpl in HLu.
      destruct (comp i j); [inversion HLu; subst; clear HLu | discriminate |].
      - simpl comp_list; rewrite assoc, (comm (_ r2)), <- HEq; reflexivity.
      - simpl comp_list; rewrite <- IHrs by eauto using SS_tail.
        rewrite !assoc, (comm (_ r2)); reflexivity.
    Qed.

    Definition state_sat (r: res) σ: Prop := ✓r /\
      match r with
        | (ex_own s, _) => s = σ
        | _ => True
      end.

    Global Instance state_sat_dist : Proper (equiv ==> equiv ==> iff) state_sat.
    Proof.
      intros [ [s1| |] r1] [ [s2| |] r2] [EQs EQr] σ1 σ2 EQσ; unfold state_sat; simpl in *; try tauto; try rewrite !EQs; try rewrite !EQr; try rewrite !EQσ; reflexivity.
    Qed.

    Global Instance preo_unit : preoType () := disc_preo ().

    Program Definition wsat (σ : state) (m : mask) (r : res) (w : Wld) : UPred () :=
      ▹ (mkUPred (fun n _ => exists rs : nat -f> pres,
                    state_sat (r · (comp_map rs)) σ
                      /\ forall i (Hm : m i),
                           (i ∈ dom rs <-> i ∈ dom w) /\
                           forall π ri (HLw : w i == Some π) (HLrs : rs i == Some ri),
                             ı π w n ri) _).
    Next Obligation.
      intros n1 n2 _ _ HLe _ [rs [HLS HRS] ]. exists rs; split; [assumption|].
      setoid_rewrite HLe; eassumption.
    Qed.

    Global Instance wsat_equiv σ : Proper (meq ==> equiv ==> equiv ==> equiv) (wsat σ).
    Proof.
      intros m1 m2 EQm r r' EQr w1 w2 EQw [| n] []; [reflexivity |].
      split; intros [rs [HE HM] ]; exists rs.
      - split; [rewrite <-EQr; assumption | intros; apply EQm in Hm; split; [| setoid_rewrite <- EQw; apply HM, Hm] ].
        destruct (HM _ Hm) as [HD _]; rewrite HD; clear - EQw.
        rewrite fdLookup_in; setoid_rewrite EQw; rewrite <- fdLookup_in; reflexivity.
      - split; [rewrite EQr; assumption | intros; apply EQm in Hm; split; [| setoid_rewrite EQw; apply HM, Hm] ].
        destruct (HM _ Hm) as [HD _]; rewrite HD; clear - EQw.
        rewrite fdLookup_in; setoid_rewrite <- EQw; rewrite <- fdLookup_in; reflexivity.
    Qed.

    Global Instance wsat_dist n σ m r : Proper (dist n ==> dist n) (wsat σ m r).
    Proof.
      intros w1 w2 EQw [| n'] [] HLt; [reflexivity |]; destruct n as [| n]; [now inversion HLt |].
      split; intros [rs [HE HM] ]; exists rs.
      - split; [assumption | split; [rewrite <- (domeq _ _ _ EQw); apply HM, Hm |] ].
        intros; destruct (HM _ Hm) as [_ HR]; clear HE HM Hm.
        assert (EQπ := EQw i); rewrite HLw in EQπ; clear HLw.
        destruct (w1 i) as [π' |]; [| contradiction]; do 3 red in EQπ.
        apply ı in EQπ; apply EQπ; [now auto with arith |].
        apply (met_morph_nonexp _ _ (ı π')) in EQw; apply EQw; [now auto with arith |].
        apply HR; [reflexivity | assumption].
      - split; [assumption | split; [rewrite (domeq _ _ _ EQw); apply HM, Hm |] ].
        intros; destruct (HM _ Hm) as [_ HR]; clear HE HM Hm.
        assert (EQπ := EQw i); rewrite HLw in EQπ; clear HLw.
        destruct (w2 i) as [π' |]; [| contradiction]; do 3 red in EQπ.
        apply ı in EQπ; apply EQπ; [now auto with arith |].
        apply (met_morph_nonexp _ _ (ı π')) in EQw; apply EQw; [now auto with arith |].
        apply HR; [reflexivity | assumption].
    Qed.

    Lemma wsat_not_empty σ m (r: res) w k :
      wsat σ m r w (S k) tt -> ✓r.
    Proof.
      intros [rs [HD _] ]. destruct HD as [VAL _].
      eapply ra_op_valid; [now apply _|]. eassumption.
    Qed.

  End WorldSatisfaction.

  Notation " p @ k " := ((p : UPred ()) k tt) (at level 60, no associativity).

End IrisCore.
