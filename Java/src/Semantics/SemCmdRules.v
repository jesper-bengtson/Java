Require Import SemCmd ILogic BILogic ILInsts BILInsts. 
Require Import OpenILogic Later AssertionLogic SpecLogic ILEmbed Open.
Require Import Stack Subst Lang Util List.
Require Import FunctionalExtensionality Traces.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Ltac solve_atom :=
	match goal with 
		| |- ?P => first [has_evar P | reflexivity | omega | assumption | idtac]
	end.
    
Ltac solve_model_aux := 
	match goal with
		| |- ?P ?a |-- ?Q ?b =>
			 first [apply ILPreFrm_fold_entails; [solve_atom|solve_model_aux] | 
			        apply ILFun_fold_entails; [solve_atom|solve_model_aux]]
	    | |- ?P |-- ?Q => try reflexivity
	end.

Ltac solve_model x :=
	let H := fresh "H" in
	match goal with 
		| |- ?Q => let P := type of x in
						assert (P |-- Q) as H; [solve_model_aux|apply H; apply x]
						
    end.


Open Scope open_scope.

	Local Transparent ILPre_Ops.
    Local Transparent ILFun_Ops.
	Local Transparent BILPre_Ops.
    Local Transparent BILFun_Ops.
    Local Transparent ILLaterPreOps.
    Local Transparent ILLaterNatOps.


Section Rules.

  Section StructuralRules.

    Lemma rule_of_consequence (P P' Q Q' : sasn) (c : semCmd)
      (HPre  : P  |-- P')
      (HPost : Q' |-- Q ) :
      {{P'}}c{{Q'}} |-- {{P}}c{{Q}}.
    Proof.
      intros n Pr Hc Pr' m k s h t HPr Hmn Hkm HP; simpl.
      destruct (Hc _ _ _ s h t HPr Hmn Hkm) as [HSafe HQ].
      + apply HPre; apply HP.
      + split; [apply HSafe|intros t' h' s' H]. (* split. *)
        - apply HPost. specialize (HQ _ _ _ H). apply HQ.
        (* - specialize (HQ _ _ _ H). apply HQ. *)
    Qed.

    Definition not_modifies (c : semCmd) (x : var) : Prop :=
      forall PP s s' h h' t t' n (HSem : c PP n s h t (Some (s', (h', t')))),
        s x = s' x.

    Lemma frame_rule : forall P Q R c (xs: list var)
      (HMod : forall x, ~ In x xs -> not_modifies c x),
      {{ P }} c {{ Q }} |--
      {{ P ** R }} c {{ Q ** Exists vs, apply_subst R (subst_fresh vs xs) }}.
    Proof.
      intros.
      intros PP n HSpec PP' ? ? ? ? ? HPP' Hmn Hkm [h1 [h2 [HSub [HP HR]]]]; split.
      (* safety *)
      { destruct (HSpec _ m k s h t HPP' Hmn Hkm) as [HS _]; [ | assumption].
        solve_model HP. exists h2; apply HSub.
      }
      (* correctness *)
      intros ? ? ? HSem. 
      destruct (@cmd_frame c PP' s s' h h' h2 h1 k t t') as [h'' [HBig Hc]]. 
      + assumption.
      + intros l Hle.
        destruct (HSpec _ m l s h1 t HPP' Hmn) as [HS _]; [ omega | assumption |].
        apply HS.
      + assumption.
      + destruct (HSpec _ m k s h1 t HPP' Hmn Hkm) as [_ HC]. 
        * apply HP.
        * specialize (HC t' h'' s' Hc).
          (* destruct HC as [HC Hst].
          split; [| assumption]. *)
          exists h'', h2, HBig. split; [assumption |].
          simpl. exists s. unfold apply_subst.
          solve_model HR.
          - unfold Rel.rel, MapInterface.Equal.
            intros x.
            admit (* fangel, tasn *).
          - apply functional_extensionality. intros x.
            unfold stack_subst, subst_fresh.
            destruct (in_dec Rel.dec_eq x xs) as [|HNotIn]; [reflexivity|].
            unfold not_modifies in HMod. 
            specialize (HMod _ HNotIn _ _ _ _ _ _ _ _ HSem).
            apply HMod.
    Qed.

    Lemma conj_rule G P1 P2 Q1 Q2 c 
      (H1 : G |-- {{P1}} c {{Q1}})
      (H2 : G |-- {{P2}} c {{Q2}}) :
      G |-- {{P1 //\\ P2}} c {{Q1 //\\ Q2}}.
    Proof.
      intros n P HPP HG.
      simpl. intros m k s h t HPP' Hm Hk [HP1 HP2]. split.
      + eapply H1; eauto.
      + intros t' h' s' Hsem.
        (* split *)
        - split; [eapply H1|eapply H2]; eauto.
        (* - edestruct H1; try eassumption.
          specialize (H0 t' h' s' Hsem).
          apply H0. *)
    Qed.

  End StructuralRules.

  Section PrimitivesRules.

    Lemma skip_rule P : |-- {{P}}skip_cmd {{P}}.
    Proof.
      intros n Pr HPP Pr' m k s h t _ Hmn Hkm HP; split.
      + intros H; inversion H.
      + intros t' h' s' HSem; inversion HSem; subst.
        (* split; [|intros; assumption]. *)
        solve_model HP.
    Qed.

    Lemma seq_rule c1 c2 P Q R :
      ({{P}}c1{{Q}} //\\ {{Q}}c2{{R}}) |-- {{P}}seq_cmd c1 c2{{R}}.
    Proof.
      intros Pr n [Hc1 Hc2] Pr' k m s h t HPP' Hmn Hkm HP; split.
      + intros HFail; inversion HFail; subst; clear HFail.	
        * destruct (Hc1 _ _ n0 s h t HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; assumption ].
        * destruct (Hc1 _ _ n0 s h t HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ _ H).
          destruct (Hc2 _ (k - n0) n' s' h' t' HPP') as [HS _]; [omega | omega | |].
          apply HC. 
          apply HS; exact H0.
      + intros t' h' s' HSem; inversion HSem; subst; clear HSem.
        destruct (Hc1 _ _  n0 s h t HPP' Hmn) as [_ HC1]; [omega | assumption |].
        specialize (HC1 _ _ _ H6) (*; destruct HC1 as [HC1 Hst1] *).
        destruct (Hc2 _ (k - n0) n1 s1 h1 t1 HPP') as [_ HC2]; [omega | omega | |].
        apply HC1.
        specialize (HC2 _ _ _ H8) (*; destruct HC2 as [HC2 Hst2] *).
        (* split. *)
        * solve_model HC2.
        (* * intuition. *) 
    Qed.

    Lemma nondet_rule c1 c2 P Q:
      ({{P}}c1{{Q}} //\\ {{P}}c2{{Q}}) |-- {{P}}nondet_cmd c1 c2{{Q}}.
    Proof.
      intros n Pr [Hc1 Hc2] Pr' k m s h t HPP' Hmn Hkm HP; split.
      + intros HFail; inversion HFail; subst; clear HFail.
        * destruct (Hc1 _ _ n0 s h t HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; assumption].
        * destruct (Hc2 _ _ n0 s h t HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; assumption].
      + intros h1 s1 t1 HSem; inversion HSem; subst; clear HSem.
        * destruct (Hc1 _ _ n0 s h t HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ _ H5) (*; destruct HC as [HC Hst] *). 
          solve_model HC.
          (* split; [ solve_model HC | assumption ]. *)
        * destruct (Hc2 _ _ n0 s h t HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ _ H5) (*; destruct HC as [HC Hst] *).
           solve_model HC.
          (* split; [ solve_model HC | assumption ]. *)
    Qed.

    Lemma kleene_rule c P:
      {{P}}c{{P}} |-- {{P}} kleene_cmd c {{P}}.
    Proof.
      intros Pr n Hc Pr' m k s h t HPP' Hmn Hkm Hp; split.
      + intros HFail. generalize dependent m. remember None as cfg.
        induction HFail; intros; inversion Heqcfg; subst.
        * destruct (Hc _ m n0 s h t HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; assumption].
        * destruct (Hc _ m n0 s h t HPP' Hmn) as [_ HC]; [omega | assumption |].
          apply IHHFail with (m-n0); [assumption | reflexivity | omega | omega | ].
          specialize (HC _ _ _ H) (*; destruct HC as [HC Hst] *).
          solve_model HC.
      + intros. remember (Some (s', (h', t'))) as cfg. generalize dependent m. 
        induction H; inversion Heqcfg; subst; intros.
        * solve_model Hp.
          (* split; [ solve_model Hp | intuition ]. *)
        * destruct (Hc _ m n0 s h t HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ _ H) (*; destruct HC as [HC Hst] *).
          assert ((((P s') t' P0) ((m - n0) - n1)) h') as H2. 
            apply IHkleene_sem; try assumption; try omega. 
          (* assert ( (STs_traces P0 (st s') t' -> STs_traces P0 (st s0) t0)).
            apply IHkleene_sem with (m := m - n0); try assumption; try omega. *)
          solve_model H2.
          (* split; [ solve_model H2 | intuition]. *)
    Qed.

    Lemma assume_rule P (t : vlogic) :
      |-- {{P}} assume_cmd t {{t /\\ P}}.
    Proof.
      intros n Pr Hc Pr' m k s h tr HPP' Hmn Hkm Hp; split.
      + intros HFail. inversion HFail.
      + intros tr' h' s' H. remember (Some (s', (h', tr'))) as cfg; induction H.
        inversion Heqcfg; subst; intros.
        (* split; [| intuition]. *)
        split; [assumption|]. solve_model Hp.
    Qed.

    Lemma assert_rule (P : sasn) (p : vlogic) (HPe : P |-- embed p) :
      |-- {{P}} assert_cmd p {{P}}.
    Proof.
      intros n Pr Hc Pr' m k s h t HPP' Hmn Hkm Hp; specialize (HPe _ _ _ _ _ Hp); split.
      + intros HF; inversion HF; subst; auto.
      + intros t' h' s' HSem; inversion HSem; subst.
        solve_model Hp.
        (* split; [ solve_model Hp | intuition ]. *)
    Qed.

  End PrimitivesRules.

  Lemma exists_into_precond {A} (P: A -> sasn) c q :
    (Forall x, {{P x}} c {{q}}) -|- {{Exists x, P x}} c {{q}}.
  Proof.
  	split.
  	+ intros n Pr Hp Pr' m k s h t HPP' Hmn Hkm [x Hxp]; specialize (Hp x); auto.
  	+ intros n Pr Hp x Pr' m k s h t HPP' Hmn Hkm Hxp.
  	  apply Hp; try assumption. exists x; apply Hxp.
  Qed.

  (* Holds only in one direction unless annotations on assertion logic, which is ugly - well, it's happened. - F.
     This is the important direction, though *)
  Lemma I_precond (SP : spec) (P Q : sasn) c:
    (SP -->> {{ P }} c {{ Q }}) -|- {{ SP /\\  P }} c {{ Q }}.
  Proof.
  	split.
  	+ intros Pr n Hp Pr' m k s h t HPP' Hmn Hkm [HSP HP].
  	  specialize (Hp Pr' HPP' m Hmn HSP).
  	  apply Hp; reflexivity || assumption.
  	+ intros Pr n Hp Pr' HPP' m Hnm HSP Pr'' k l s h t HPP'' Hkm Hkl HP.
  	  apply Hp.
  	  * transitivity Pr'; assumption.
  	  * omega.
  	  * omega.
  	  * simpl. split. 
        assert ((SP Pr'') k). solve_model HSP. intros a b. simpl. intuition.
        apply H. apply HP.
  Qed.

End Rules.
