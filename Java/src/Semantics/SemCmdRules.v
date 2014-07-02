Require Import SemCmd ILogic BILogic ILInsts BILInsts. 
Require Import OpenILogic Later ProtocolLogic AssertionLogic SpecLogic ILEmbed Open.
Require Import Stack Subst Lang Util Lists.List.
Require Import FunctionalExtensionality ST Traces.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Open Scope open_scope.

	Local Transparent ILPre_Ops.
    Local Transparent ILFun_Ops.
	Local Transparent BILPre_Ops.
    Local Transparent BILFun_Ops.
    Local Transparent ILLaterPreOps.
    Local Transparent ILLaterNatOps.
    Local Transparent EmbedPSasnSasnOp.
    Local Transparent EmbedILFunDropOp.
    Local Transparent EmbedILFunOp.
    
Section Rules.

  Section StructuralRules.

    Lemma rule_of_consequence (P P' Q Q' : psasn) (c : semCmd)
      (HPre  : P  |-- P')
      (HPost : Q' |-- Q ) :
      {{P'}}c{{Q'}} |-- {{P}}c{{Q}}.
    Proof.
      intros n Pr Hc Pr' m k s h cl pr HPr Hmn Hkm HP; simpl.
      destruct (Hc _ _ _ s h cl pr HPr Hmn Hkm) as [HSafe HQ].
      + apply HPre; apply HP.
      + split; [apply HSafe|intros tr h' s' cl' H].
        eapply Comp_entails; [intros; apply HPost; apply H0 |].
        specialize (HQ _ _ _ _ H). apply HQ.
    Qed.

	Local Existing Instance EmbedPSasnSasnOp.

    Definition not_modifies (c : semCmd) (x : var) : Prop :=
      forall PP s s' h h' cl cl' tr n (HSem : c PP n s h cl tr (Some (s', (h', cl')))),
        s x = s' x.

    (*
    Lemma frame_rule : forall (P Q R : psasn) c (xs: list var)
      (HMod : forall x, ~ In x xs -> not_modifies c x),
      {{ P }} c {{ Q }} |--
      {{ P ** R }} c {{ Q ** Exists vs, apply_subst R (subst_fresh vs xs) }}.
    Proof.
      intros.
      (* Should have something with [T1 T2 TSub], where (T1 T2 : STs) and (TSub: sa_mul T1 T2 STs) *)
      intros PP n HSpec PP' ? ? ? ? ? pr HPP' Hmn Hkm [h1 [h2 [HSub [HP HR]]]]; split.
      (* safety *)
      { destruct (HSpec _ m k s h cl pr HPP' Hmn Hkm) as [HS _]; [ | assumption].
        solve_model HP. exists h2; apply HSub.
      }
      (* correctness *)
      intros ? ? ? ? HSem. 
      
      (* Should be given STs STs' T2 T1 instead *)
      unfold sem_triple in HSpec. simpl in HSpec.
      destruct (HSpec PP' m k s h1 cl pr HPP' Hmn Hkm HP) as [HSafe HComp]; clear HSpec.
      specialize (HSafe tr). specialize (HComp tr). clear -HSafe HComp HR HSub HSem.
      
      induction c; simpl in *.
      
      
      
      destruct (HSpec _ m l s h1 cl pr HPP' Hmn) as [HS _]; [ omega | solve_model HP; exists h2; assumption | ].
      destruct (@cmd_frame c PP' s s' h h' h2 h1 cl cl' k tr) as [h'' [HBig Hc]]. 
      + assumption.
      + intros l Hle.
        destruct (HSpec _ m l s h1 cl pr HPP' Hmn) as [HS _]; [ omega | solve_model HP; exists h2; assumption | ].
        intros ? ? Htr Hfail.
        specialize (HS _ _ Hfail).
        
        admit (* fangel, used, frame-rule, oh-boy-safety-fun *).
        (*
        rewrite Htr in HSem.
        clear HP HR Hfail Htr. generalize dependent pr. generalize dependent tr. generalize dependent tr''.
        induction tr'; intros tr'' HSem tr pr HS; simpl in HS; [ apply HS; reflexivity | ..].
        remember (MapInterface.find s0 pr ); destruct o; [| assumption]; destruct s1; try assumption; destruct HS as [_ HS].
        specialize (IHtr' _ _ HSem Htr).
        
        
        destruct (HSpec _ m k s h pr HPP' Hmn) as [_ HComp]; [ omega | solve_model HP; exists h2; assumption | ].
        specialize (HComp _ _ _ HSem).
        assert (c PP' k s h1 tr (Some (s', h'))) by admit (* fangel, used, test *).
        specialize (HS tr (Some (s', h')) _ Hle H).
        
        apply HS. *)
      + assumption.
      + (* should be T1 instead of STs *)
        destruct (HSpec _ m k s h1 pr HPP' Hmn Hkm) as [_ HC]. 
        * apply HP.
        * specialize (HC _ _ _ Hc).
          eapply Comp_entails; [| apply HC].
          intros.
          exists h'', h2, HBig.
          split; [apply H |].
          simpl. exists s. unfold apply_subst, id.
          simpl in HR. 
          solve_model HR.
          - admit (* fangel, used, frame-rule *).
          - apply functional_extensionality. intros x.
            unfold stack_subst, subst_fresh.
            destruct (in_dec Rel.dec_eq x xs) as [|HNotIn]; [reflexivity|].
            unfold not_modifies in HMod. 
            specialize (HMod _ HNotIn _ _ _ _ _ _ _ HSem).
            apply HMod.
    Qed.
    *)
    
    Lemma conj_rule G P1 P2 Q1 Q2 c 
      (H1 : G |-- {{P1}} c {{Q1}})
      (H2 : G |-- {{P2}} c {{Q2}}) :
      G |-- {{P1 //\\ P2}} c {{Q1 //\\ Q2}}.
    Proof.
      intros n P HPP HG.
      simpl. intros m k s h cl pr HPP' Hm Hk [HP1 HP2]. split.
      + eapply H1; eauto.
      + intros tr h' s' cl' Hsem.
        specialize (H1 _ _ HPP); specialize (H1 _ _ _ _ _ cl _ HPP' Hm Hk HP1); destruct H1 as [_ H1]; specialize (H1 _ _ _ _ Hsem).
        specialize (H2 _ _ HPP); specialize (H2 _ _ _ _ _ cl _ HPP' Hm Hk HP2); destruct H2 as [_ H2]; specialize (H2 _ _ _ _ Hsem).
        eapply Comp_split; eassumption.
    Qed.

  End StructuralRules.

  Section PrimitivesRules.

    Lemma skip_rule P : |-- {{P}}skip_cmd {{P}}.
    Proof.
      intros n Pr HPP Pr' m k s h cl pr _ Hmn Hkm HP; split.
      + intros tr cfg H; inversion H; subst; congruence.
      + intros tr h' s' cl' HSem; inversion HSem; subst; simpl.
        solve_model HP.
    Qed.

    Lemma seq_rule c1 c2 P Q R :
      ({{P}}c1{{Q}} //\\ {{Q}}c2{{R}}) |-- {{P}}seq_cmd c1 c2{{R}}.
    Proof.
      intros Pr n [Hc1 Hc2] Pr' k m s h cl pr HPP' Hmn Hkm HP; split.
      + intros tr cfg H. destruct cfg.  
        * inversion H; subst; clear H.
          destruct (Hc1 _ _ n0 s h cl pr HPP' Hmn) as [_ HC1]; [omega | solve_model HP |]; specialize (HC1 _ _ _ _ H1).
          assert (n0 = trace_length tr0) by admit (* fangel, fuel = trace-length *).
          eapply Comp_partial; [eassumption | eassumption | apply HC1 |].
          intros; simpl in H0.
          destruct (Hc2 _ n1 n1 s1 h1 cl1 pr0 HPP') as [_ HC2]; [omega | omega | solve_model H0 |]; specialize (HC2 _ _ _ _ H8).
          eapply Comp_entails; [congruence | apply HC2].
        * inversion H; subst; clear H.
          - destruct (Hc1 _ _ m s h cl pr HPP' Hmn) as [HS _]; [omega | assumption |]; specialize (HS _ _ H0); assumption.
          - destruct (Hc1 _ _ n0 s h cl pr HPP' Hmn) as [_ HC1]; [omega | solve_model HP |]; specialize (HC1 _ _ _ _ H0).
            assert (n0 = trace_length tr0) by admit (* fangel, fuel = trace-length *).
            eapply Comp_partial; [ eassumption | eassumption | apply HC1 |].
            intros; simpl in H.
            destruct (Hc2 _ n' n' s' h' cl' pr0 HPP') as [HS _]; [omega | omega | solve_model H2 |]; specialize (HS _ _ H1); assumption.
      + intros tr h' s' cl' HSem; inversion HSem; subst; clear HSem.
        destruct (Hc1 _ _ n0 s h cl pr HPP' Hmn) as [_ HC1]; [omega | solve_model HP |]; specialize (HC1 _ _ _ _ H7).
        assert (n0 = trace_length tr0) by admit (* fangel, fuel = trace-length *).
        eapply Comp_partial; [ eassumption | eassumption | apply HC1 |].
        intros; simpl in H.
        destruct (Hc2 _ n1 n1 s1 h1 cl1 pr0 HPP') as [_ HC2]; [omega | omega | solve_model H0 |]; specialize (HC2 _ _ _ _ H9).
        eapply Comp_entails; [| apply HC2].
        intros; simpl in H0.
        solve_model H1.
    Qed.

    Lemma nondet_rule c1 c2 P Q:
      ({{P}}c1{{Q}} //\\ {{P}}c2{{Q}}) |-- {{P}}nondet_cmd c1 c2{{Q}}.
    Proof.
      intros n Pr [Hc1 Hc2] Pr' k m s h cl pr HPP' Hmn Hkm HP; split.
      + intros tr cfg Hsem.
        destruct cfg; inversion Hsem; subst.
        * destruct (Hc1 _ _ m s h cl pr HPP' Hmn) as [HS _]; [omega | assumption |]; specialize (HS _ _ H6); assumption.
        * destruct (Hc2 _ _ m s h cl pr HPP' Hmn) as [HS _]; [omega | assumption |]; specialize (HS _ _ H6); assumption.
        * destruct (Hc1 _ _ m s h cl pr HPP' Hmn) as [HS _]; [omega | assumption |]; specialize (HS _ _ H).
          induction tr; simpl; simpl in HS; [congruence | | | apply HS | auto];
          (remember (MapInterface.find s0 pr); destruct o; [| assumption]; destruct s1; assumption).
        * destruct (Hc2 _ _ m s h cl pr HPP' Hmn) as [HS _]; [omega | assumption |]; specialize (HS _ _ H).
          induction tr; simpl; simpl in HS; [congruence | | | apply HS | auto];
          (remember (MapInterface.find s0 pr); destruct o; [| assumption]; destruct s1; assumption).
      + intros tr h1 s1 cl1 HSem; inversion HSem; subst; clear HSem.
        * destruct (Hc1 _ _ m s h cl pr HPP' Hmn) as [_ HC]; [omega | assumption |]; specialize (HC _ _ _ _ H6).
          eapply Comp_entails; [| apply HC].
          intros; simpl in H; solve_model H. 
        * destruct (Hc2 _ _ m s h cl pr HPP' Hmn) as [_ HC]; [omega | assumption |]; specialize (HC _ _ _ _ H6).
          eapply Comp_entails; [| apply HC].
          intros; simpl in H; solve_model H. 
    Qed.

    Lemma kleene_rule c P:
      {{P}}c{{P}} |-- {{P}} kleene_cmd c {{P}}.
    Proof.
      intros Pr n Hc Pr' m k s h cl pr HPP' Hmn Hkm Hp; split.
      + intros tr cfg HSem.
        generalize dependent pr. generalize dependent m.
        induction HSem; simpl; intros.
        - congruence.
        - destruct (Hc _ m n0 s h cl pr HPP' Hmn Hkm Hp) as [HS _]. 
          apply HS; assumption.
        - assert (n0 = trace_length tr) by admit (* fangel, trace-length *).
          destruct (Hc _ _ n0 s h cl pr HPP' Hmn) as [_ HC]; [omega | solve_model Hp |]; specialize (HC _ _ _ _ H).
          eapply Comp_partial; [ eassumption | eassumption | apply HC |]. 
          intros. simpl in H1.
          eapply IHHSem; [ assumption | | reflexivity | apply H1]; omega.
        - assert (n0 = trace_length tr) by admit (* fangel, trace-length *).
          destruct (Hc _ _ n0 s h cl pr HPP' Hmn) as [_ HC]; [omega | solve_model Hp |]; specialize (HC _ _ _ _ H).
          eapply Comp_partial; [ eassumption | eassumption | apply HC |].
          intros. simpl in H1.
          eapply IHHSem; [ assumption | | reflexivity | apply H1]; omega.
      + intros. remember (Some (s', (h', cl'))) as cfg. generalize dependent m. generalize dependent pr.
        induction H; inversion Heqcfg; subst; intros.
        * simpl. solve_model Hp.
        * assert (n0 = trace_length tr) by admit (* fangel, trace-length *).
          destruct (Hc _ _ n0 s h cl pr HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ _ _ H).
          eapply Comp_partial; [ eassumption | eassumption | apply HC |].
          intros. simpl in H2.
          apply IHkleene_sem; [ assumption | reflexivity | | reflexivity | apply H2]; omega.
    Qed.
    
    Lemma assume_rule P (t : vlogic) :
      |-- {{P}} assume_cmd t {{t /\\ P}}.
    Proof.
      intros n Pr Hc Pr' m k s h cl pr HPP' Hmn Hkm Hp; split.
      + intros; inversion H; subst; simpl. congruence.
      + intros tr' h' s' cl' H. remember (Some (s', (h', cl'))) as cfg; induction H; simpl.
        inversion Heqcfg; subst; clear Heqcfg; intros.
        split; [assumption|]. solve_model Hp.
    Qed.

    Lemma assert_rule (P : psasn) (p : vlogic) (HPe : P |-- embed p) :
      |-- {{P}} assert_cmd p {{P}}.
    Proof.
      intros n Pr Hc Pr' m k s h cl pr HPP' Hmn Hkm Hp; specialize (HPe _ _ _ _ _ Hp); split.
      + intros; inversion H; subst; simpl; [ congruence | auto].
      + intros tr h' s' cl' HSem; inversion HSem; subst; simpl.
        solve_model Hp.
    Qed.
    
  End PrimitivesRules.

  Lemma exists_into_precond {A} (P: A -> psasn) c q :
    (Forall x, {{P x}} c {{q}}) -|- {{Exists x, P x}} c {{q}}.
  Proof.
  	split.
  	+ intros n Pr Hp Pr' m k s h cl pr HPP' Hmn Hkm [x Hxp]; specialize (Hp x); auto.
  	+ intros n Pr Hp x Pr' m k s h cl pr HPP' Hmn Hkm Hxp.
  	  apply Hp; try assumption. exists x; apply Hxp.
  Qed.

  (* Holds only in one direction unless annotations on assertion logic, which is ugly - well, it's happened. - F.
     This is the important direction, though *)
  Lemma I_precond (SP : spec) (P Q : psasn) c:
    (SP -->> {{ P }} c {{ Q }}) -|- {{ SP /\\  P }} c {{ Q }}.
  Proof.
  	split.
  	+ intros Pr n Hp Pr' m k s h cl pr HPP' Hmn Hkm [HSP HP].
  	  specialize (Hp Pr' HPP' m Hmn HSP).
  	  apply Hp; reflexivity || assumption.
  	+ intros Pr n Hp Pr' HPP' m Hnm HSP Pr'' k l s h cl pr HPP'' Hkm Hkl HP.
  	  apply Hp.
  	  * transitivity Pr'; assumption.
  	  * omega.
  	  * omega.
  	  * simpl. split. 
        assert ((SP Pr'') k). solve_model HSP. intros a b. simpl. intuition.
        apply H. apply HP.
  Qed.

End Rules.
