Require Import SemCmd ILogic BILogic ILInsts BILInsts.
Require Import OpenILogic Later AssertionLogic SpecLogic ILEmbed.
Require Import Stack Charge.Open.Subst Lang Util List.
Require Import FunctionalExtensionality.
Require Import Model.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Open Scope open_scope.

Section Rules.

  Section StructuralRules.

    Lemma rule_of_consequence (P P' Q Q' : sasn) (c : semCmd)
      (HPre  : P  |-- P')
      (HPost : Q' |-- Q ) :
      {{P'}}c{{Q'}} |-- {{P}}c{{Q}}.
    Proof.
	  lintros n Pr. 
      intros Hc Pr' m k s h HPr Hmn Hkm HP; simpl.
      destruct (Hc _ _ _ s h HPr Hmn Hkm) as [HSafe HQ].
	  + ilapply HPre; apply HP.
      + split; [apply HSafe|intros h' s' H]. 
	    ilapply HPost; apply HQ; apply H.
    Qed.

    Definition not_modifies (c : semCmd) (x : var) : Prop :=
      forall PP s s' h h' n (HSem : c PP n s h (Some (s', h'))),
        s x = s' x.

    Lemma frame_rule : forall P Q R c (xs: list var)
      (HMod : forall x, ~ In x xs -> not_modifies c x),
      {{ P }} c {{ Q }} |--
      {{ P ** R }} c {{ Q ** Exists vs, apply_subst R (subst_fresh vs xs) }}.
    Proof.
      admit.
      (*
      intros.
      intros ? PP HSpec PP' ? ? ? ? HPP' Hmn Hkm [h1 [h2 [HSub [HP HR]]]]; split.
      (* safety *)
      { destruct (HSpec _ m k s h HPP' Hmn Hkm) as [HS _]; [ | assumption].
        solve_model HP. exists h2; apply HSub.
      }
      (* correctness *)
      intros ? ? HSem. 
      destruct (@cmd_frame c PP' s s' h h' h2 h1 k) as [h'' [HBig Hc]]. 
      + assumption.
      + intros l Hle. destruct (HSpec _ m l s h1 HPP' Hmn) as [HS _];
        assumption || omega.
      + assumption.
      + destruct (HSpec _ m k s h1 HPP' Hmn Hkm) as [_ HC]. 
        * apply HP.
        * specialize (HC h'' s' Hc).
          exists h'', h2, HBig. split. assumption.
          simpl. exists s. unfold apply_subst.
          solve_model HR.
          apply functional_extensionality. intros x.
          unfold stack_subst, subst_fresh.
          destruct (in_dec Rel.dec_eq x xs) as [|HNotIn]; [reflexivity|].
          simpl. unfold not_modifies in HMod. eapply HMod; eassumption.
          *)
  Qed.
(*
    Lemma conj_rule G P1 P2 Q1 Q2 c 
      (H1 : G |-- {{P1}} c {{Q1}})
      (H2 : G |-- {{P2}} c {{Q2}}) :
      G |-- {{P1 //\\ P2}} c {{Q1 //\\ Q2}}.
    Proof.
      lintros n P.
      intros HPP HG.
      simpl. intros m k s h HPP' Hm Hk [HP1 HP2]. split.
      + eapply H1; eauto.
      + split; [eapply H1|eapply H2]; eauto.
    Qed.
*)
  End StructuralRules.

  Section PrimitivesRules.

(* These should preferably go away *)
Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.
Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.


    Lemma skip_rule P : |-- {{P}}skip_cmd {{P}}.
    Proof.
	  lintros n Pr.
      intros HPP Pr' m k s h _ Hmn Hkm HP; split.
      + intro H; inversion H.
      + intros h' s' HSem; inversion HSem; subst.
      	solve_model HP.
    Qed.

    Lemma seq_rule c1 c2 P Q R :
      ({{P}}c1{{Q}} //\\ {{Q}}c2{{R}}) |-- {{P}}seq_cmd c1 c2{{R}}.
    Proof.
      lintros n PR.
      intros [Hc1 Hc2] Pr' k m s h HPP' Hmn Hkm HP; split.
      + intro HFail; inversion HFail; subst; clear HFail.
        * destruct (Hc1 _ _ n0 s h HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; exact H].
        * destruct (Hc1 _ _ n0 s h HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ H).
          destruct (Hc2 _ (k - n0) n' s' h' HPP') as [HS _]; [omega | omega | |].
          apply HC. apply HS. exact H0.
      + intros h1 s1 HSem; inversion HSem; subst; clear HSem.
        destruct (Hc1 _ _ n0 s h HPP' Hmn) as [_ HC1]; [omega | assumption |].
        specialize (HC1 _ _ H5).
        destruct (Hc2 _ (k - n0) n1 s2 h2 HPP') as [_ HC2]; [omega | omega | |].
        apply HC1. specialize (HC2 _ _ H6).
        solve_model HC2.
    Qed.

    Lemma nondet_rule c1 c2 P Q :
      ({{P}}c1{{Q}} //\\ {{P}}c2{{Q}}) |-- {{P}}nondet_cmd c1 c2{{Q}}.
    Proof.
      lintros n Pr.
      intros [Hc1 Hc2] Pr' k m s h HPP' Hmn Hkm HP; split.
      + intro HFail; inversion HFail; subst; clear HFail.
        * destruct (Hc1 _ _ n0 s h HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; exact H].
        * destruct (Hc2 _ _ n0 s h HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; exact H].
      + intros h1 s1 HSem; inversion HSem; subst; clear HSem.
        * destruct (Hc1 _ _ n0 s h HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ H4). solve_model HC.
        * destruct (Hc2 _ _ n0 s h HPP' Hmn) as [_ HC]; [omega | assumption |].
          specialize (HC _ _ H4). solve_model HC.
    Qed.

    Lemma kleene_rule c P :
      {{P}}c{{P}} |-- {{P}} kleene_cmd c {{P}}.
    Proof.
      lintros n Pr.
      intros Hc Pr' m k s h HPP' Hmn Hkm Hp; split.
      + intro HFail. generalize dependent m. remember None as cfg.
        induction HFail; intros; inversion Heqcfg; subst.
        * destruct (Hc _ m n0 s h HPP' Hmn) as [HS _];
          [omega | assumption | apply HS; exact H].
        * destruct (Hc _ m n0 s h HPP' Hmn) as [_ HC]; [omega | assumption |].
          apply IHHFail with (m-n0); [assumption | reflexivity | omega | omega | ].
          specialize (HC _ _ H). solve_model HC.
      + intros. remember (Some (s', h')) as cfg. generalize dependent m. 
        induction H; inversion Heqcfg; subst; intros.
        * solve_model Hp.
        * destruct (Hc _ m n0 s h HPP' Hmn) as [_ HC]; [omega | assumption |].
          assert ((((P s') P0) ((m - n0) - n1)) h') as H1. 
          apply IHkleene_sem; try assumption; try omega. apply HC; assumption.
          solve_model H1.
    Qed.

    Lemma assume_rule P (t : vlogic) :
      |-- {{P}} assume_cmd t {{t /\\ P}}.
    Proof.
      lintros n Pr.
      intros Hc Pr' m k s h HPP' Hmn Hkm Hp; split.
      + intros HFail. inversion HFail.
      + intros h' s' H. remember (Some (s', h')) as cfg; induction H.
        inversion Heqcfg; subst; intros.
        split; [assumption|]. solve_model Hp.
    Qed.

    Lemma assert_rule (P : sasn) (p : vlogic) (HPe : P |-- embed p) :
      |-- {{P}} assert_cmd p {{P}}.
    Proof.
      lintros n Pr.
      intros Hc Pr' m k s h HPP' Hmn Hkm Hp; specialize (HPe _ _ _ _ Hp); split.
      + intro HF; inversion HF; subst; auto.
      + intros h' s' HSem; inversion HSem; subst. solve_model Hp.
    Qed.

  End PrimitivesRules.

  Lemma exists_into_precond {A} (P: A -> sasn) c q :
    (Forall x, {{P x}} c {{q}}) -|- {{Exists x, P x}} c {{q}}.
  Proof.
    admit.
    (*
  	split.
  	+ lintros n Pr; intros Hp Pr' m k s h HPP' Hmn Hkm [x Hxp]; specialize (Hp x); auto.
  	+ lintros n Pr. intro Hp. intro x. Pr' m k s h HPP' Hmn Hkm Hxp.
  	  apply Hp; try assumption. exists x; apply Hxp.
*)
  Qed.

  (* Holds only in one direction unless annotations on assertion logic, which is ugly - well, it's happened. - F.
     This is the important direction, though *)
  Lemma I_precond (SP : spec) (P Q : sasn) c :
    (SP -->> {{ P }} c {{ Q }}) -|- {{ SP /\\  P }} c {{ Q }}.
  Proof.
    admit.
    (*
  	split.
  	+ lintros Pr n. intros Hp Pr' m k s h HPP' Hmn Hkm [HSP HP].
  	  specialize (Hp Pr' HPP' m Hmn HSP).
  	  apply Hp; reflexivity || assumption.
  	+ lintros Pr n; intros Hp. intro Pr'. HPP' m Hnm HSP Pr'' k l s h HPP'' Hkm Hkl HP.
  	  apply Hp.
  	  * transitivity Pr'; assumption.
  	  * omega.
  	  * omega.
  	  * simpl. split. 
        assert ((SP Pr'') k). solve_model HSP. intros a b. simpl. intuition.
        apply H. apply HP.
	*)
  Qed.

End Rules.
