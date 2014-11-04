Require Import Later Program ILogic ILEmbed ILInsts Lang RelationClasses.

(*
Local Existing Instance ILLaterNat.
Local Existing Instance ILLaterNatOps.
Local Existing Instance ILLaterPre.
Local Existing Instance ILLaterPreOps.
Local Existing Instance ILPre_Ops.
Local Existing Instance ILPre_ILogic.
*)

Require Import AssertionLogic.

Definition context := list comp_cmd.

Fixpoint cmd_to_context c :=
  match c with 
    | cc_seq c1 c2 => (cmd_to_context c1) ++ (cmd_to_context c2)
    | cc_skip => nil
    | _ => c::nil
  end.

Definition ext_cont (c1 c2 : context) := exists c3, c1 = (c2 ++ c3).

Instance ext_cont_Pre: PreOrder ext_cont.
Proof.
 split.
 - exists nil; simpl; rewrite app_nil_r; reflexivity.
 - intros c1 c2 c3 [c4 H1] [c5 H2]. exists (c5 ++ c4).
   rewrite H2, <- app_assoc in H1; apply H1.
Qed.

(*
Global Instance ILLOperatorsSpec : ILLOperators spec := _.
Global Instance ILogicOpsSpec : ILogicOps spec := _. 
Global Instance ILSpec : ILLater spec := _.
*)

Local Transparent ILPre_Ops.
Local Transparent ILFun_Ops.
Require Import Compare_dec.

Inductive ST :=
  | st_end : ST
  | st_send : var -> sasn -> ST -> ST
  | st_recv : var -> sasn -> ST -> ST.
  
Inductive label :=
  | l_tau : label
  | l_send : channel -> val -> heap -> label
  | l_recv : channel -> val -> heap -> label
  | l_start : channel -> comp_cmd -> label.
  
Inductive par_context :=
  | pc_atom : stack -> heap -> context -> par_context
  | pc_nu : channel -> par_context -> par_context -> par_context.
  
Inductive hole_context :=
  | hc_hole : hole_context
  | hc_nu1 : channel -> hole_context -> par_context -> hole_context
  | hc_nu2 : channel -> par_context -> hole_context -> hole_context.

Fixpoint hc_to_pc (hc : hole_context) pc : par_context :=
	match hc with
	  | hc_hole => pc
	  | hc_nu1 a c1 c2 => pc_nu a (hc_to_pc c1 pc) c2
	  | hc_nu2 a c1 c2 => pc_nu a c1 (hc_to_pc c2 pc)
	end.

Definition label_channel l :=
  match l with
	| l_tau =>  None
	| l_send c _ _ => Some c
	| l_recv c _ _ => Some c
	| l_start c _ => Some c
  end.

Fixpoint pc_channels (pc : par_context) : list channel :=
  match pc with
    | pc_atom _ _ _ => nil
    | pc_nu c pc1 pc2 => c :: pc_channels pc1 ++ pc_channels pc2
  end.

Definition wf_par_context pc := NoDup (pc_channels pc).
 
Fixpoint hc_channels (hc : hole_context) : list channel :=
  match hc with
    | hc_hole => nil
    | hc_nu1 c hc pc => c :: hc_channels hc ++ pc_channels pc
    | hc_nu2 c pc hc => c :: pc_channels pc ++ hc_channels hc
  end.

Definition list_disjoint {A : Type} (l1 l2 : list A) := 
	List.Forall (fun a => ~In a l1) l2.
	
Lemma list_disjoint_nil (A : Type) (l : list A) :
	list_disjoint nil l.
Proof.
  induction l; constructor; [|apply IHl].
  intros H. inversion H.
Qed.

Lemma list_disjoint_consI (A : Type) (x : A) (l1 l2 : list A) 
	(H : list_disjoint l1 l2) (Hx : ~In x l2) :
	list_disjoint (x::l1) l2.
Proof.
  induction H; constructor.
  + intros H1. 
    induction H1; subst; [
      apply Hx; constructor; reflexivity |
      apply H; apply H1
    ].
  + apply IHForall. intros H1. apply Hx.
  	right; apply H1.
Qed.

Lemma list_disjoint_sym (A : Type) (l1 l2 : list A)
	(H : list_disjoint l1 l2) : list_disjoint l2 l1.
Proof.
  induction H.
  + apply list_disjoint_nil.
  + simpl.
    apply list_disjoint_consI; assumption.
Qed.

Lemma list_disjoint_consE (A : Type) (x : A) (l1 l2 : list A) 
	(H : list_disjoint (x::l1) l2) : 
	~In x l2 /\ list_disjoint l1 l2.
Proof.
  apply list_disjoint_sym in H.
  inversion H; subst.
  split; [|apply list_disjoint_sym]; assumption.
Qed.

Lemma Forall_appE {A : Type} P (l1 l2 : list A)
	(H : List.Forall P (l1 ++ l2)) : 
	List.Forall P l1 /\ List.Forall P l2.
Proof.
  induction l1; simpl in *.
  + split; [constructor | assumption].
  + inversion H; subst.
    destruct (IHl1 H3) as [H4 H5].
    split; [constructor|]; assumption.
Qed.

Lemma Forall_appI {A : Type} P (l1 l2 : list A)
    (H1 : List.Forall P l1) (H2 : List.Forall P l2) :
	List.Forall P (l1 ++ l2). 
Proof.
  induction l1; simpl in *; [assumption|].
  inversion H1; subst. constructor; [|apply IHl1]; assumption.
Qed.

Lemma list_disjoint_appE (A : Type) (l1 l2 l3 : list A) 
	(H : list_disjoint (l1 ++ l2) l3) :
	list_disjoint l1 l3 /\ list_disjoint l2 l3.
Proof.
  apply list_disjoint_sym in H.
  apply Forall_appE in H.
  destruct H as [H1 H2].
  split; apply list_disjoint_sym; [apply H1|apply H2].
Qed.

Lemma list_disjoint_appI (A : Type) (l1 l2 l3 : list A) 
	(H1 : list_disjoint l1 l3) (H2 : list_disjoint l2 l3) :
	list_disjoint (l1 ++ l2) l3.
Proof.
  apply list_disjoint_sym.
  SearchAbout List.Forall app.
  apply Forall_appI; apply list_disjoint_sym; [apply H1 | apply H2].
Qed.

Definition wf_hole_context hc := NoDup (hc_channels hc).

Lemma NoDup_appE {A : Type} (l1 l2 : list A)  (H : NoDup (l1 ++ l2)) :
	NoDup l1 /\ NoDup l2 /\ list_disjoint l1 l2.
Proof.
  induction l1; simpl in *.
  + repeat split; [constructor | assumption | apply list_disjoint_nil].
  + inversion H; subst.
    specialize (IHl1 H3). destruct IHl1 as [Hl1 [Hl2 Hdisj]].
    repeat split; [|assumption|].
    * constructor. intros Ha.
      apply H2. apply in_app_iff; left; assumption.
      assumption.
    * apply list_disjoint_consI; [assumption|].
      intros Ha. apply H2. apply in_app_iff; right; assumption.
Qed.

Lemma NoDup_appI {A : Type} (l1 l2 : list A) 
	(Hl1 : NoDup l1) (Hl2 : NoDup l2) (Hdisj : list_disjoint l1 l2) :
    NoDup (l1 ++ l2).
Proof.
  induction l1; simpl in *; [assumption|].
  inversion Hl1; subst. constructor.
  + intros H. apply in_app_or in H. destruct H; [apply H1; apply H|].
    apply list_disjoint_sym in Hdisj. inversion Hdisj; subst.
    apply H4; apply H.
  + apply IHl1; [assumption|].
    apply list_disjoint_sym in Hdisj; inversion Hdisj; subst.
    apply list_disjoint_sym; apply H4.
Qed.

Lemma wf_hole_context_nu1E c hc pc 
	(H : wf_hole_context (hc_nu1 c hc pc)) :
	wf_hole_context hc /\ wf_par_context pc /\
	list_disjoint (hc_channels hc) (pc_channels pc) /\
	~In c (hc_channels hc) /\ ~In c (pc_channels pc).
Proof.
  inversion H; subst.
  apply NoDup_appE in H3 as [H3 [H4 H5]].
  repeat split; try assumption; intros H1; apply H2;
  apply in_app_iff; intuition.
Qed.

Lemma wf_hole_context_nu2E c hc pc 
	(H : wf_hole_context (hc_nu2 c pc hc)) :
	wf_hole_context hc /\ wf_par_context pc /\
	list_disjoint (pc_channels pc) (hc_channels hc) /\
	~In c (hc_channels hc) /\ ~In c (pc_channels pc).
Proof.
  inversion H; subst.
  apply NoDup_appE in H3 as [H3 [H4 H5]].
  repeat split; try assumption; intros H1; apply H2;
  apply in_app_iff; intuition.
Qed.

Lemma wf_par_context_parI pc1 pc2 c
	(Hpc1 : wf_par_context pc1) (Hpc2 : wf_par_context pc2)
	(Hdisj : list_disjoint (pc_channels pc1) (pc_channels pc2)) 
	(Hc1 : ~In c (pc_channels pc1)) (Hc2 : ~In c (pc_channels pc2)) :
	wf_par_context (pc_nu c pc1 pc2).
Proof.
  unfold wf_par_context in *; simpl.
  constructor.
  + intro H; apply in_app_iff in H.
  	destruct H as [H | H]; [apply Hc1 | apply Hc2]; apply H.
  + apply NoDup_appI; assumption.
Qed.

Lemma hc_to_pc_disjoint_channels (hc : hole_context) (pc : par_context) l
    (H : list_disjoint (hc_channels hc ++ pc_channels pc) l) :
	list_disjoint (pc_channels (hc_to_pc hc pc)) l.
Proof.
  induction hc; simpl in *; intros.
  + apply H.
  + rewrite <- app_assoc in H.
    apply list_disjoint_consE in H as [H H1].
    apply list_disjoint_appE in H1 as [H1 H2].
    apply list_disjoint_appE in H2 as [H2 H3].
    apply list_disjoint_consI; [|assumption].
    apply list_disjoint_appI; [|assumption].
    apply IHhc.
    apply list_disjoint_appI; assumption.
  + rewrite <- app_assoc in H.
    apply list_disjoint_consE in H as [H H1].
    apply list_disjoint_appE in H1 as [H1 H2].
    apply list_disjoint_appE in H2 as [H2 H3].
    apply list_disjoint_consI; [|assumption].
    apply list_disjoint_appI; [assumption|].
    apply IHhc.
    apply list_disjoint_appI; assumption.
Qed.

Lemma hc_to_pc_in c hc pc 
	(H : In c (pc_channels (hc_to_pc hc pc))) :
	In c (hc_channels hc) \/ In c (pc_channels pc).
Proof.
  induction hc; simpl in *.
  + right; assumption.
  + destruct H as [H | H]; subst.
    * left; left; reflexivity.
    * apply in_app_or in H as [H | H].
      specialize (IHhc H). destruct IHhc as [H1 | H1].
      - left; right; apply in_app_iff; left; assumption.
      - right; assumption.
      - left; right; apply in_app_iff; right; assumption.
  + destruct H as [H | H]; subst.
    * left; left; reflexivity.
    * apply in_app_or in H as [H | H].
      - left; right; apply in_app_iff; left; assumption.
      - specialize (IHhc H). destruct IHhc as [H1 | H1].
        left; right; apply in_app_iff; right; assumption.
        right; assumption.
Qed.

Lemma wf_hc_to_pc (hc : hole_context) (pc : par_context)
  (Hhc : wf_hole_context hc) (Hpc : wf_par_context pc)
  (H : list_disjoint (hc_channels hc) (pc_channels pc)) :
  wf_par_context (hc_to_pc hc pc).
Proof.
  induction hc; simpl in *.
  + apply Hpc.
  + pose proof H as H'.
    apply list_disjoint_consE in H; destruct H as [H H1].
    apply list_disjoint_appE in H1. destruct H1 as [H1 H2].
    apply wf_hole_context_nu1E in Hhc.
    destruct Hhc as [H3 [H4 [H5 [H6 H7]]]].
	
    apply wf_par_context_parI.
    * apply IHhc; assumption.
    * assumption.
    * apply hc_to_pc_disjoint_channels.
      apply list_disjoint_sym in H'; inversion H'; subst.
      apply list_disjoint_sym in H10. 
      apply list_disjoint_appE in H10 as [H10 H11].
      apply list_disjoint_appI.
      apply H5. apply list_disjoint_sym. apply H11.
	* intros H8. 
	  apply hc_to_pc_in in H8; destruct H8 as [H8 | H8].
	  apply H6; assumption.
	  apply H; assumption.
    * assumption.
  + pose proof H as H'.
    apply list_disjoint_consE in H; destruct H as [H H1].
    apply list_disjoint_appE in H1. destruct H1 as [H1 H2].
    apply wf_hole_context_nu2E in Hhc.
    destruct Hhc as [H3 [H4 [H5 [H6 H7]]]].
	
    apply wf_par_context_parI.
    * assumption.
    * apply IHhc; assumption.
    * apply list_disjoint_sym; 
      apply hc_to_pc_disjoint_channels.
      apply list_disjoint_sym in H'; inversion H'; subst.
      apply list_disjoint_sym in H10. 
      apply list_disjoint_appE in H10 as [H10 H11].
      apply list_disjoint_appI.
      apply list_disjoint_sym.
      apply H5. apply list_disjoint_sym; apply H10.
	* assumption.
	* intros H8.
	  apply hc_to_pc_in in H8; destruct H8 as [H8 | H8].	
	  apply H6; assumption.
	  apply H; assumption.
Qed.

Definition spec := ILPreFrm Prog_sub (ILPreFrm ge 
	(Fun context (Fun hole_context (ILPreFrm extSP Prop)))).

Definition mk_spec (f: Program -> nat -> context -> hole_context -> sasn -> Prop)
  (Hnat: forall k P c hc T, f P (S k) c hc T -> f P k c hc T)
  (HSPred: forall k P P' c hc T, Prog_sub P P' -> f P k c hc T -> f P' k c hc T)
  (HSExt: forall k P c hc T U, extSP T U -> f P k c hc T -> f P k c hc U) : spec.
  refine (mkILPreFrm (fun k => 
  		   (mkILPreFrm (fun P c hc => 
  		       (mkILPreFrm (fun T => f k P c hc T) _)) _)) _).
Proof.
  intros P P' HPP' k c. simpl. intros. eapply HSPred. eassumption. assumption.
  Grab Existential Variables.
  intros n m Hnk S'. simpl.
   generalize dependent m. induction n; intros.
  + assert (m = 0) by omega; subst. apply H.
  + destruct (gt_eq_gt_dec m (S n)) as [[H1 | H1] | H1]; [| | omega].
    * apply IHn. omega. apply Hnat. apply H.
    * subst. apply H.
  + intros; simpl. apply HSExt; assumption.
Defined.

Program Definition prog_spec (X : Program -> Prop) : spec :=
  mk_spec (fun (P : Program) _ _ _ _ => forall (Q : Program) , Prog_sub P Q -> X Q /\ valid_program Q = true) _ _ _.
Next Obligation.
  intros; apply H0; etransitivity; eassumption.
Qed.

Notation "'[prog]' P"    := (prog_spec  P) (at level 65).

Local Existing Instance EmbedILPreDropOp.
Local Existing Instance EmbedILPreDrop.
Local Existing Instance EmbedOpPropProp.
Local Existing Instance EmbedPropProp.
(*
Instance EmbedPropSpecOp : EmbedOp Prop spec := _. 
Instance EmbedPropSpec : Embed Prop spec := _.
*)
Definition prog_eq Prog : spec := [prog] (fun P => P = Prog).

Lemma prog_eq_to_prop P (f : Program -> Prop) (H : f P) : prog_eq P |-- [prog] f.
Proof.
  intros Q n c hc T HQ R HQR.
  specialize (HQ _ HQR).
  simpl in *. subst. intuition congruence.
Qed.

(* The following code is an adaptation of the coqos code by Jensen, Kennedy and Benton. *)

Require Import BILogic.
Require Import Model.

Require Import Morphisms.

Program Definition spec_at (G : spec) (R: sasn) :=
 mk_spec (fun Pr k c hc P => G Pr k c hc (R ** P)) _ _ _.
Next Obligation.
 solve_model H.
Qed.
Next Obligation.
 solve_model H0.
Qed.
Next Obligation.
 solve_model H0.
 destruct H as [V H].
 exists V. rewrite sepSPA, H; reflexivity.
Qed.

Infix "@" := spec_at (at level 44, left associativity).

Lemma spec_frame (S : spec) (R : sasn) :
 S |-- S @ R.
Proof.
 intros Pr k c hc P H. unfold spec_at; simpl.
 assert (extSP P (P ** R)) as HPR by (exists R; reflexivity).
 rewrite ->sepSPC in HPR. rewrite <-HPR. assumption.
Qed.

(* For variations of this instance with lentails instead of extSP, look at
  [spec_at_covar_m] and [spec_at_contra_m]. *)
  
Require Import Morphisms.

Instance spec_at_entails_m:
 Proper (lentails ++> extSP ++> lentails) spec_at.
Proof.
 intros S S' HS R R' HR Pr k c hc P H.
 unfold spec_at in *; simpl in H; simpl.
 solve_model H; [rewrite <- HR|rewrite <- HS]; reflexivity.
Qed.

Instance spec_at_equiv_m:
 Proper (lequiv ++> lequiv ++> lequiv) spec_at.
Proof.
 intros S S' HS R R' HR; split; cancel2; (rewrite HS || rewrite HR); reflexivity.
Qed.

Lemma spec_at_emp S: S @ empSP -|- S.
Proof.
 split; [|apply spec_frame].
 intros Pr k c hc P; unfold spec_at; simpl; rewrite empSPL; intros; assumption.
Qed.

Lemma spec_at_at S R R': S @ R @ R' -|- S @ (R ** R').
Proof.
 split; intros; unfold spec_at; simpl; intros; solve_model H; [
 	rewrite sepSPA | rewrite <- sepSPA ]; reflexivity.
Qed.

Lemma spec_at_forall {T} F R: (Forall x:T, F x) @ R -|- Forall x:T, (F x @ R).
Proof. split; simpl; intros; apply H. Qed.

Lemma spec_at_exists {T} F R: (Exists x:T, F x) @ R -|- Exists x:T, (F x @ R).
Proof. split; simpl; intros; apply H. Qed.

Lemma spec_at_true R: ltrue @ R -|- ltrue.
Proof. split; simpl; intros; apply H. Qed.

Lemma spec_at_false R: lfalse @ R -|- lfalse.
Proof. split; simpl; intros; apply H. Qed.

Lemma spec_at_and S S' R: (S //\\ S') @ R -|- (S @ R) //\\ (S' @ R).
Proof. split; simpl; intros; apply H. Qed.

Lemma spec_at_or S S' R: (S \\// S') @ R -|- (S @ R) \\// (S' @ R).
Proof. split; simpl; intros; apply H. Qed.
(*
Lemma spec_at_propimpl p S R: (p ->> S) @ R -|- p ->> (S @ R).
Proof. 
  split; simpl; intros. 
  + specialize (H _ x0 _ x2 _ x4); apply H; [rewrite x6 |assumption]; try reflexivity. 
  + specialize (H _ x0 _ x2 _ x4). rewrite <- x6. eapply H. reflexivity. assumption.
Qed.
*)
Lemma spec_at_impl S S' R: (S -->> S') @ R -|- (S @ R) -->> (S' @ R).
Proof.
 split.
 - apply limplAdj. rewrite <-spec_at_and.
   cancel2. apply landAdj. reflexivity.
 - unfold spec_at; simpl; intros Pr k c hc P H Pr' HPr' k' Hk' P' [Pext HPext] HS.
   rewrite <- HPext, sepSPA in HS.
   assert (extSP P (P ** Pext)) by (exists Pext; reflexivity).
   specialize (H _ HPr' _ Hk' _ H0 HS). rewrite sepSPA in HPext. rewrite HPext in H.
   assumption.
Qed.
