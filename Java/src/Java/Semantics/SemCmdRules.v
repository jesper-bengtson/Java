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
    
    
    Ltac opt_destruct :=
        match goal with
          | H : context [match ?trm with | Some _ => _ | None => _ end] |- _ => 
            let o := fresh "o" in remember trm as o; destruct o
        end.


Section Rules.

  Section StructuralRules.

    Lemma rule_of_consequence (P P' Q Q' : psasn) (c : semCmd)
      (HPre  : P  |-- P')
      (HPost : Q' |-- Q ) :
      {{P'}}c{{Q'}} |-- {{P}}c{{Q}}.
    Proof.
      intros n Pr Hc Pr' m s h cl pr HPr Hmn HP; simpl.
      specialize (Hc _ _ s h cl pr HPr Hmn).
      + intros.
       eapply Comp_entails; [intros; apply HPost; apply H0 |].
       apply Hc; try assumption.
       apply HPre; assumption.
    Qed.



	Local Existing Instance EmbedPSasnSasnOp.

	Fixpoint trace_not_modifies (s : stack) (x : var) (tr : trace) :=
        match tr with
          | t_end s' _ _ => s x = s' x
          | t_fail => True
          | t_tau _ _ _ tr => trace_not_modifies s x tr
          | t_send c v h tr => trace_not_modifies s x tr
          | t_recv c f => forall v h, trace_not_modifies s x (f v h)
          | t_start c tr tr' => trace_not_modifies s x tr'
        end.
		
(*
    Definition not_modifies (c : semCmd) (x : var) : Prop :=
      forall PP s h cl tr , trace_not_modifies s x tr.

*)
    
 
    Lemma frame_rule : forall (P Q R : psasn) (c : semCmd) (xs: list var)
      (HMod : forall PP s h cl tr (HSem : c PP s h cl tr) x, ~ In x xs -> trace_not_modifies s x tr),
      {{ P }} c {{ Q }} |--
      {{ P ** R }} c {{ Q ** Exists vs, apply_subst R (subst_fresh vs xs) }}.
    Proof with eauto.
      intros.
      intros P' n HSem P'' m s big cl STs HP'P'' Hmn HPR tr Hc. 
      destruct HPR as [pr [prframe [HPRFrame [h [frame [HFrame [HP HR]]]]]]].
      edestruct (@cmd_frame c)... destruct H as [H1 H2].
      specialize (HSem P'' m s h cl pr HP'P'' Hmn HP _ H2).
      specialize (HMod P'' s big cl tr Hc).
      clear -HSem HR H1 HPRFrame HFrame HMod.
      generalize dependent m; generalize dependent STs. generalize dependent pr. induction H1; intros; admit.
      (*
      + inversion HSem.
      + inversion HSem.
      + simpl in HSem. destruct tr.
        - inversion H1; subst.
          exists pr, prframe, HPRFrame, h0, frame, H.
          split; [apply HSem|]. simpl.
          exists s. unfold apply_subst.
          solve_model HR.
          apply functional_extensionality. intros.
          specialize (HMod x). simpl in HMod.
          unfold subst_fresh, stack_subst.
          destruct (in_dec Rel.dec_eq x xs) as [|HNotIn]; [reflexivity|].
          apply HMod; assumption.
        - simpl in HSem. destruct HSem. 
        - inversion H1; subst.
          eapply IHframe_trace; try eassumption.
          solve_model HR.
        - inversion H1; subst.
          eapply IHframe_trace; try eassumption.
          solve_model HR.
        - inversion H1; subst.
          eapply IHframe_trace; try eassumption.
          solve_model HR.
        - inversion H1; subst.
          eapply IHframe_trace; try eassumption.
          solve_model HR.
      + unfold stptr, protocol in *.
        simpl in HSem.
        opt_destruct; [|destruct HSem].
		destruct s0; destruct HSem. pose proof HPRFrame.
        simpl in HPRFrame. specialize (HPRFrame x). opt_destruct.
        destruct HPRFrame as [[H4 H5] | [H4 H5]].
        rewrite Maps.MF.find_mapsto_iff in H4.
        unfold stptr in *.
        rewrite H4 in Heqo. inversion Heqo; subst.
        simpl. unfold stptr. rewrite <- Heqo0. 
        split. solve_model H0. exists frame. assumption.
        eapply IHframe_trace; try eassumption.
        Require Import Charge.SepAlg.SepAlgMap.
        apply sa_mul_add. assumption. assumption.
        solve_model HR.
        rewrite Maps.MF.in_find_iff in H5. contradict H5. intros HNone.
        unfold stptr in *. rewrite HNone in Heqo. congruence.
        destruct HPRFrame as [H9 _]. contradict H9.
        rewrite Maps.MF.in_find_iff. intros HNone. unfold stptr in *. rewrite HNone in Heqo. 
        congruence.
      + unfold stptr, protocol in *.
        simpl in HSem.
        opt_destruct; [|destruct HSem].
        destruct s0; try destruct HSem.
        assert (MapInterface.find c STs = Some (st_recv v s0 s1)) by admit.
        simpl. unfold stptr, protocol in *. rewrite H1.
        intros; eapply H0; try eassumption; [intros; eapply HMod; eassumption| | eapply HSem; apply H2 | solve_model HR].
		apply sa_mul_add; try assumption.
		specialize (HPRFrame c). 
		opt_destruct.
		destruct HPRFrame as [HPRFrame | [H3 H4]]; [tauto|].
		contradict H4. rewrite Maps.MF.in_find_iff. intros HNone. rewrite HNone in Heqo. congruence.
		tauto.
      + admit.*)
   Qed.
      
(*    
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
*)
  End StructuralRules.

  Section PrimitivesRules.

    Lemma skip_rule P : |-- {{P}}skip_cmd {{P}}.
    Proof.
      intros n Pr HPP Pr' m s h cl pr _ Hmn HP tr HSem.
      inversion HSem; subst; simpl.
      solve_model HP.
    Qed.

      Lemma trace_append_cmd_Comp Pr Pr' m n P Q tr tr' pr c
          (HPr : Program.Prog_wf_sub Pr Pr') (Hmn : m <= n) (H : Comp Pr' m pr tr P) 
          (HTriple : ({{P}} c {{Q}}) Pr n) (Htrace : trace_append_cmd Pr' c tr tr') :
          Comp Pr' m pr tr' Q.
      Proof.
      generalize dependent tr'; generalize dependent pr; generalize dependent m; induction tr; intros.
      + inversion Htrace; subst.
        simpl in H.
        assert (P s pr Pr' (m - 1) h) by solve_model H.
		assert (m - 1 <= n) by omega.
        specialize (HTriple _ (m - 1) s h t pr HPr H1 H0 _ H4).
		simpl; destruct tr; simpl in *; try congruence.
      + simpl in H. destruct H.
      + inversion Htrace; subst.
        simpl in H. 
        opt_destruct; [|inversion H].
        destruct s0; destruct H.
        simpl. rewrite <- Heqo.
        split; [assumption|].
        apply IHtr; try omega; assumption.
      + inversion Htrace; subst.
        simpl in H0.
        opt_destruct; [|inversion H0].
        destruct s0; try destruct H0.
        simpl; rewrite <- Heqo. intros.
        eapply H; try omega. apply H0. eassumption. apply H4.
      + inversion Htrace. admit.
      + inversion Htrace; subst.
        assert (m - 1 <= n) by omega.
        specialize (IHtr _ H0).
        destruct tr; simpl in *; inversion H5; subst. 
        - simpl in *. eapply HTriple; try eassumption. omega.
		- apply IHtr; assumption. 
        - apply IHtr; assumption.
        - apply IHtr; assumption.
		- apply IHtr; assumption.
		- apply IHtr; assumption.
      Qed.

    Lemma seq_rule c1 c2 P Q R :
      ({{P}}c1{{Q}} //\\ {{Q}}c2{{R}}) |-- {{P}}seq_cmd c1 c2{{R}}.
    Proof.
      intros Pr n [Hc1 Hc2] Pr' m s h cl pr HPP' Hmn HP tr Hcmd.
      inversion Hcmd; subst. clear Hcmd.
      specialize (Hc1 _ _ s h cl pr HPP' Hmn HP tr0 H).
      clear HP H.
      eapply trace_append_cmd_Comp; eassumption.
    Qed.

    Lemma nondet_rule c1 c2 P Q:
      ({{P}}c1{{Q}} //\\ {{P}}c2{{Q}}) |-- {{P}}nondet_cmd c1 c2{{Q}}.
    Proof.
      intros Pr n [Hc1 Hc2] Pr' m s h cl pr HPP' Hmn HP tr Hcmd. inversion Hcmd; subst.
      + specialize (Hc1 _ _ s h cl pr HPP' Hmn HP _ H). apply Hc1.
      + specialize (Hc2 _ _ s h cl pr HPP' Hmn HP _ H). apply Hc2.
    Qed.

    Lemma kleene_rule c P:
      {{P}}c{{P}} |-- {{P}} kleene_cmd c {{P}}.
    Proof. 
      intros Pr n Hc Pr' m k s h cl pr HPP' Hmn tr HSem. 
      generalize dependent pr; generalize dependent m.
      induction HSem; simpl; intros.
      - solve_model Hmn.
      - eapply trace_append_cmd_Comp; try eassumption.
        simpl in Hc. eapply Hc; eassumption.
    Qed.

    Lemma assume_rule P (t : vlogic) :
      |-- {{P}} assume_cmd t {{t /\\ P}}.
    Proof.
      intros Pr n Hc Pr' m s h cl pr HPP' Hmn Hp tr Hcmd.
      inversion Hcmd; subst.
      simpl. split. assumption. solve_model Hp.
    Qed.

    Lemma assert_rule (P : psasn) (p : vlogic) (HPe : P |-- embed p) :
      |-- {{P}} assert_cmd p {{P}}.
    Proof.
      intros n Pr Hc Pr' m s h cl pr HPP' Hmn Hp tr Hcmd. 
	  specialize (HPe _ _ _ _ _ Hp).
	  inversion Hcmd; subst. simpl. solve_model Hp.
	  simpl in *. apply HNP. apply HPe.
    Qed.
    
  End PrimitivesRules.

  Lemma exists_into_precond {A} (P: A -> psasn) c q :
    (Forall x, {{P x}} c {{q}}) -|- {{Exists x, P x}} c {{q}}.
  Proof.
  	split.
  	+ intros Pr n Hc Pr' m s h cl pr HPP' Hmn [x Hp] tr HSem. specialize (Hc x).
  	  simpl in *. eapply Hc; eassumption.
  	+ intros Pr n Hc x Pr' m k s h cl HPP' Hmn  Hxp tr HSem.
  	  simpl in Hc; eapply Hc; try eassumption. exists x; apply Hxp.
  Qed.

  (* Holds only in one direction unless annotations on assertion logic, which is ugly - well, it's happened. - F.
     This is the important direction, though *)
  Lemma I_precond (SP : spec) (P Q : psasn) c:
    (SP -->> {{ P }} c {{ Q }}) -|- {{ SP /\\  P }} c {{ Q }}.
  Proof.
  	split.
  	+ intros n Pr Hc Pr' m k s h cl HPP' Hmn [HSP HP] tr HSem.
  	  specialize (Hc Pr' HPP' m Hmn HSP).
  	  simpl in Hc. eapply Hc; reflexivity || eassumption.
  	+ intros Pr n Hc Pr' HPP' m Hnm HSP Pr'' l s h pr cl HPP'' Hlm HP tr HSem.
  	  simpl in Hc; eapply Hc.
  	  * transitivity Pr'; assumption.
  	  * omega.
  	  * simpl. split. 
        assert ((SP Pr'') l). solve_model HSP. intros a b. simpl. intuition.
        apply H. apply HP. 
      * eassumption.
  Qed.

End Rules.
