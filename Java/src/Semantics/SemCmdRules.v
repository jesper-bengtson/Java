Require Import SemCmd ILogic BILogic ILInsts BILInsts. 
Require Import OpenILogic Later ProtocolLogic AssertionLogic SpecLogic ILEmbed Open.
Require Import Stack Subst Lang Util List.
Require Import FunctionalExtensionality Traces.

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

Section Rules.

  Section StructuralRules.

    Lemma rule_of_consequence (P P' Q Q' : psasn) (c : semCmd)
      (HPre  : P  |-- P')
      (HPost : Q' |-- Q ) :
      {{P'}}c{{Q'}} |-- {{P}}c{{Q}}.
    Proof.
      intros n Pr Hc Pr' PM m k s h t HPr Hmn Hkm HP; simpl.
      destruct (Hc _ PM _ _ s h t HPr Hmn Hkm) as [HSafe HQ].
      + apply HPre; apply HP.
      + split; [apply HSafe|intros t' h' s' H].
        apply HPost. specialize (HQ _ _ _ H). apply HQ.
    Qed.

    Definition not_modifies (c : semCmd) (x : var) : Prop :=
      forall PP PM s s' h h' t t' n (HSem : c PP PM n s h t (Some (s', (h', t')))),
        s x = s' x.
        
    Lemma frame_rule : forall (P Q : psasn) (R : sasn) c (xs: list var)
      (HMod : forall x, ~ In x xs -> not_modifies c x),
      {{ P }} c {{ Q }} |--
      {{ P ** embed R }} c {{ Q ** Exists vs, embed (apply_subst R (subst_fresh vs xs)) }}.
    Proof.
      intros.
      intros PP n HSpec PP' ? ? ? ? ? ? HPP' Hmn Hkm [h1 [h2 [HSub [HP HR]]]]; split.
      (* safety *)
      { destruct (HSpec _ PM m k s h t HPP' Hmn Hkm) as [HS _]; [ | assumption].
        solve_model HP. exists h2; apply HSub.
      }
      (* correctness *)
      intros ? ? ? HSem. 
      destruct (@cmd_frame c PP' PM s s' h h' h2 h1 k t t') as [h'' [HBig Hc]]. 
      + assumption.
      + intros l Hle.
        destruct (HSpec _ PM m l s h1 t HPP' Hmn) as [HS _]; [ omega | assumption |].
        apply HS.
      + assumption.
      + destruct (HSpec _ PM m k s h1 t HPP' Hmn Hkm) as [_ HC]. 
        * apply HP.
        * specialize (HC t' h'' s' Hc).
          exists h'', h2, HBig. split; [assumption |].
          simpl. exists s. unfold apply_subst, id.
          simpl in HR; unfold id in HR.
          solve_model HR.
          - unfold Rel.rel, MapInterface.Equal.
            intros x.
            admit (* fangel, tasn *).
          - apply functional_extensionality. intros x.
            unfold stack_subst, subst_fresh.
            destruct (in_dec Rel.dec_eq x xs) as [|HNotIn]; [reflexivity|].
            unfold not_modifies in HMod. 
            specialize (HMod _ HNotIn _ PM _ _ _ _ _ _ _ HSem).
            apply HMod.
    Qed.

    Lemma conj_rule G P1 P2 Q1 Q2 c 
      (H1 : G |-- {{P1}} c {{Q1}})
      (H2 : G |-- {{P2}} c {{Q2}}) :
      G |-- {{P1 //\\ P2}} c {{Q1 //\\ Q2}}.
    Proof.
      intros n P HPP HG.
      simpl. intros PM m k s h t HPP' Hm Hk [HP1 HP2]. split.
      + eapply H1; eauto.
      + intros t' h' s' Hsem.
        split; [eapply H1|eapply H2]; eauto.
    Qed.

  End StructuralRules.

  Section PrimitivesRules.

    Lemma skip_rule P : |-- {{P}}skip_cmd {{P}}.
    Proof.
      intros PM n Pr HPP Pr' m k s h t _ Hmn Hkm HP; split.
      + intros H; inversion H.
      + intros t' h' s' HSem; inversion HSem; subst.
        solve_model HP.
    Qed.

    Lemma seq_rule c1 c2 P Q R :
      ({{P}}c1{{Q}} //\\ {{Q}}c2{{R}}) |-- {{P}}seq_cmd c1 c2{{R}}.
    Proof.
      intros Pr n [Hc1 Hc2] Pr' PM k m s h t HPP' Hmn Hkm HP; split.
      + intros HFail; inversion HFail; subst; clear HFail.	
        * destruct (Hc1 _ PM _ n0 s h t HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; assumption ].
        * destruct (Hc1 _ PM _ n0 s h t HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ _ H).
          destruct (Hc2 _ PM (k - n0) n' s' h' t' HPP') as [HS _]; [omega | omega | |].
          apply HC. 
          apply HS; exact H0.
      + intros t' h' s' HSem; inversion HSem; subst; clear HSem.
        destruct (Hc1 _ PM _ n0 s h t HPP' Hmn) as [_ HC1]; [omega | assumption |].
        specialize (HC1 _ _ _ H7).
        destruct (Hc2 _ PM (k - n0) n1 s1 h1 t1 HPP') as [_ HC2]; [omega | omega | |].
        apply HC1.
        specialize (HC2 _ _ _ H9).
        solve_model HC2. 
    Qed.

    Lemma nondet_rule c1 c2 P Q:
      ({{P}}c1{{Q}} //\\ {{P}}c2{{Q}}) |-- {{P}}nondet_cmd c1 c2{{Q}}.
    Proof.
      intros n Pr [Hc1 Hc2] Pr' PM k m s h t HPP' Hmn Hkm HP; split.
      + intros HFail; inversion HFail; subst; clear HFail.
        * destruct (Hc1 _ PM _ n0 s h t HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; assumption].
        * destruct (Hc2 _ PM _ n0 s h t HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; assumption].
      + intros h1 s1 t1 HSem; inversion HSem; subst; clear HSem.
        * destruct (Hc1 _ PM _ n0 s h t HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ _ H6). 
          solve_model HC.
        * destruct (Hc2 _ PM _ n0 s h t HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ _ H6).
          solve_model HC.
    Qed.

    Lemma kleene_rule c P:
      {{P}}c{{P}} |-- {{P}} kleene_cmd c {{P}}.
    Proof.
      intros Pr n Hc Pr' PM m k s h t HPP' Hmn Hkm Hp; split.
      + intros HFail. generalize dependent m. remember None as cfg.
        induction HFail; intros; inversion Heqcfg; subst.
        * destruct (Hc _ PM m n0 s h t HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; assumption].
        * destruct (Hc _ PM m n0 s h t HPP' Hmn) as [_ HC]; [omega | assumption |].
          apply IHHFail with (m-n0); [assumption | reflexivity | omega | omega | ].
          specialize (HC _ _ _ H).
          solve_model HC.
      + intros. remember (Some (s', (h', t'))) as cfg. generalize dependent m. 
        induction H; inversion Heqcfg; subst; intros.
        * solve_model Hp.
        * destruct (Hc _ PM m n0 s h t HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ _ H).
          assert ((((P PM s') t' Pr0) ((m - n0) - n1)) h') as H2. 
            apply IHkleene_sem; try assumption; try omega. 
          solve_model H2.
    Qed.

    Lemma assume_rule P (t : vlogic) :
      |-- {{P}} assume_cmd t {{t /\\ P}}.
    Proof.
      intros n Pr Hc Pr' PM m k s h tr HPP' Hmn Hkm Hp; split.
      + intros HFail. inversion HFail.
      + intros tr' h' s' H. remember (Some (s', (h', tr'))) as cfg; induction H.
        inversion Heqcfg; subst; intros.
        split; [assumption|]. solve_model Hp.
    Qed.

    Lemma assert_rule (P : psasn) (p : vlogic) (HPe : P |-- embed p) :
      |-- {{P}} assert_cmd p {{P}}.
    Proof.
      intros n Pr Hc Pr' PM m k s h t HPP' Hmn Hkm Hp; specialize (HPe _ _ _ _ _ _ Hp); split.
      + intros HF; inversion HF; subst; auto.
      + intros t' h' s' HSem; inversion HSem; subst.
        solve_model Hp.
    Qed.

  End PrimitivesRules.

  Lemma exists_into_precond {A} (P: A -> psasn) c q :
    (Forall x, {{P x}} c {{q}}) -|- {{Exists x, P x}} c {{q}}.
  Proof.
  	split.
  	+ intros n Pr Hp Pr' PM m k s h t HPP' Hmn Hkm [x Hxp]; specialize (Hp x); auto.
  	+ intros n Pr Hp x Pr' PM m k s h t HPP' Hmn Hkm Hxp.
  	  apply Hp; try assumption. exists x; apply Hxp.
  Qed.

  (* Holds only in one direction unless annotations on assertion logic, which is ugly - well, it's happened. - F.
     This is the important direction, though *)
  Lemma I_precond (SP : spec) (P Q : psasn) c:
    (SP -->> {{ P }} c {{ Q }}) -|- {{ SP /\\  P }} c {{ Q }}.
  Proof.
  	split.
  	+ intros Pr n Hp Pr' PM m k s h t HPP' Hmn Hkm [HSP HP].
  	  specialize (Hp Pr' HPP' m Hmn HSP).
  	  apply Hp; reflexivity || assumption.
  	+ intros Pr n Hp Pr' HPP' m Hnm HSP Pr'' PM k l s h t HPP'' Hkm Hkl HP.
  	  apply Hp.
  	  * transitivity Pr'; assumption.
  	  * omega.
  	  * omega.
  	  * simpl. split. 
        assert ((SP Pr'') k). solve_model HSP. intros a b. simpl. intuition.
        apply H. apply HP.
  Qed.

End Rules.
