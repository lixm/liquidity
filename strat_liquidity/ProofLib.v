
Require Import BuildUtils.
Require Import Blockchain.
Require Import Serializable.
Require Import ResultMonad.
Require Import ChainedList.

Require Import ModelBase.
Require Import StratModel. 

Require Import LibTactics. 

Definition ProtectWrapper (a:Type) : Type :=a.
Lemma MakeProtectWrapper : forall H, H -> ProtectWrapper H.
Proof.
  auto.
Qed.
Ltac protect H := let H' := fresh in rename H into H'; lets H : MakeProtectWrapper H'; clear H'.
Ltac unprotect H := unfold ProtectWrapper in H.

Lemma impl_lem:
  forall P Q,
    (P /\ ~Q) -> ~(P->Q).
Proof.
  intros.
  introv Hf.
  destruct H.
  tauto.
Qed.

Context {BaseTypes : ChainBase}.

Lemma in_list_tl_in_list:
  forall (l: list Action) act, 
    List.In act (List.tl l) -> List.In act l.
Proof.
  destruct l.
  introv Hf. simpl in Hf. false.
  introv Hin.
  simpl in Hin.
  simpl. right; auto.
Qed.

Lemma in_act_org_frm:
  forall l (a: Action) orig fr,  
    List.In a (List.map (build_act orig fr) l) ->
    a.(act_origin) = orig /\ a.(act_from) = fr.
Proof.
  induction l.
  -
    intros.
    simpl in H.
    false. 
  -
    introv Hin.
    simpl in Hin.
    destruct Hin as [Hhd | Htl].
    + subst a0.
      simpl.
      auto.
    + eapply IHl; eauto.
Qed.

Lemma adr_neq_reflect:
  forall x y, 
    address_neqb x y = true <-> x <> y. 
Proof.
  intros.
  unfold address_neqb.
  pose proof address_eqb_spec x y.
  destruct H; subst.
  simpl. intuition.
  simpl. intuition.
Qed.     

Lemma address_not_contract_negb:
  forall addr,
    address_not_contract addr= true -> address_is_contract addr = false.
Proof.
  intros.
  unfold address_not_contract in H.
  destruct ((address_is_contract addr)) eqn : H'; try congruence.
  simpl in H.
  congruence.
Qed.

Lemma addr_ctr_diff:
  forall a1 a2, 
    address_is_contract a1 = true ->
    address_not_contract a2 = true ->
    (a1 =? a2)%address = false.
Proof.
  introv Hc1 Hc2.
  eapply address_not_contract_negb in Hc2; eauto.
  destruct (a1 =? a2)%address eqn: E; auto.
  lets H__: address_eqb_spec a1 a2.
  inverts H__; 
    tryfalse.
Qed.         

Lemma addr_ctr_neq:
  forall a1 a2, 
    address_is_contract a1 = true ->
    address_not_contract a2 = true ->
    a1 <> a2. 
Proof.
  introv Hc1 Hc2.
  pose proof addr_ctr_diff a1 a2.
  specializes H; eauto.
  rewrite <- address_eq_ne' in H.
  auto.
Qed.         

Lemma contract_deployed_preservation :
  forall from to addr wc,
    inhabited (ChainTrace from to) -> 
    env_contracts from addr = Some wc ->
    env_contracts to addr = Some wc.
Proof.
  intros * [trace] deployed.
  induction trace as [ | from mid to trace IH step ].
  - assumption.
  - destruct_chain_step;
      only 2: destruct_action_eval;
      rewrite_environment_equiv; cbn;
      destruct_address_eq; subst; try easy ;eauto.    
    now rewrite IH in not_deployed by assumption.
Qed.

Lemma contract_deployed_preserved_by_act :
  forall (from t ss: ChainState) addr wc a acs,
    execute_action a from = Ok t -> 
    chain_state_queue from = (a :: acs)%list -> 
    ss = {| chain_state_env := t; chain_state_queue := chain_state_queue t ++ acs |} -> 
    env_contracts from addr = Some wc ->
    env_contracts ss addr = Some wc.
Proof.
  introv Hexea Hq1 Hss Hec.
  assert (inhabited (ChainTrace from ss)).
  {
    subst.
    constructors.
    eapply snoc; eauto.
    eapply clnil; eauto.
    eapply step_action; eauto.
    lets H__: execute_action_step Hexea; eauto.
  }
  eapply contract_deployed_preservation; eauto.
Qed.

Lemma contract_nondeployed_preservation :
  forall from to addr,
    inhabited (ChainTrace from to) -> 
    address_not_contract addr = true -> 
    env_contracts from addr = None ->
    env_contracts to addr = None.
  intros * [trace] notctr deployed.
  induction trace as [ | from mid to trace IH step ].
  - assumption.
  - destruct_chain_step.
    rewrite_environment_equiv; cbn.
    eapply IH; eauto.
    destruct_action_eval.
    rewrite_environment_equiv; cbn.
    eapply IH; eauto.
    rewrite_environment_equiv; cbn.
    {
      destruct_address_eq.
      subst.
      2: eauto.
      apply address_not_contract_negb in notctr.
      false. 
    }
    rewrite_environment_equiv; cbn.
    eauto.
    rewrite_environment_equiv; cbn.
    eauto.
    rewrite_environment_equiv; cbn.
    eauto.
Qed. 

Lemma contract_nondeployed_preserved_by_act:
  forall (from t ss: ChainState) addr a acs,
    execute_action a from = Ok t ->
    chain_state_queue from = (a :: acs)%list -> 
    ss = {| chain_state_env := t; chain_state_queue := chain_state_queue t ++ acs |} -> 
    address_not_contract addr = true -> 
    env_contracts from addr = None ->
    env_contracts ss addr = None.
Proof.
  introv Hexea Hq1 Hss Hnadr Hec.
  assert (inhabited (ChainTrace from ss)).
  {
    subst.
    constructors.
    eapply snoc; eauto.
    eapply clnil; eauto.
    eapply step_action; eauto.
    lets H__: execute_action_step Hexea; eauto.
  }
  eapply contract_nondeployed_preservation; eauto.
Qed.

Tactic Notation "destruct_head" hyp(H) ident(E) tactic(tac) :=
  match type of H with
  | context [match ?expr with _ => _ end] =>
      destruct expr eqn:E; tac
  end.

Tactic Notation "destruct_cond" hyp(H) ident(E) tactic(tac) :=
  match type of H with
  | context[if ?expr then _ else _] =>
      destruct expr eqn:E; tac
  end.

Lemma exe_act_gen_same_orig:
  forall a s s', 
    execute_action a s = Ok s' ->
    forall act,
      List.In act s'.(chain_state_queue) -> 
      a.(act_origin) = act.(act_origin).
Proof.
  introv Hexe Hin.
  unfolds in Hexe.
  destruct a eqn: Ea.
  simpl.
  destruct act_body eqn: Eb.
  -
    unfolds in Hexe.
    destruct_cond Hexe Hamlt tryfalse.
    destruct_cond Hexe Hamgt tryfalse.
    destruct_head Hexe Hec tryfalse.
    destruct_head Hexe Hecs tryfalse.
    destruct_head Hexe Hww tryfalse.
    destruct t. inverts Hexe.
    simpl in Hin.
    apply in_act_org_frm in Hin.
    destruct Hin; congruence.
    destruct_cond Hexe Haic tryfalse.
    inverts Hexe.
    simpl in Hin.
    false.
  -
    unfolds in Hexe.
    destruct_cond Hexe Hamlt tryfalse.
    destruct_cond Hexe Hamgt tryfalse.
    destruct_head Hexe Hec tryfalse.
    destruct_head Hexe Hecs tryfalse.
    destruct_head Hexe Hww tryfalse.
    destruct t. inverts Hexe.
    simpl in Hin.
    apply in_act_org_frm in Hin.
    destruct Hin; congruence.
    destruct_cond Hexe Haic tryfalse.
  -
    unfolds in Hexe.
    destruct_cond Hexe Hamlt tryfalse.
    destruct_cond Hexe Hamgt tryfalse.
    destruct_head Hexe Ead tryfalse.
    destruct_cond Hexe Ecca tryfalse.
    destruct_head Hexe Ewi tryfalse. 
    inverts Hexe.
    simpl in Hin.
    false.
Qed. 

Class ContractCls := { 
    ctr_setup : Type; 
    Hctr_ser_setup: Serializable ctr_setup; 
    ctr_msg: Type; 
    Hctr_ser_msg: Serializable ctr_msg; 
    ctr_state: Type; 
    Hctr_ser_state: Serializable ctr_state;
    ctr_error: Type; 
    Hctr_ser_err: Serializable ctr_error; 

    ctrCtr: Contract ctr_setup ctr_msg ctr_state ctr_error;
  }. 

Inductive ctr_recv_st_upd `{ContractCls}: ctr_state -> ctr_state -> Prop :=

| RcvRefl (cs: ctr_state): ctr_recv_st_upd cs cs 

| RcvUpd (cs1 cs2 cs3: ctr_state):
    forall chain ctx msg acts, 
      ctrCtr.(receive) chain ctx cs1 msg = Ok (cs2, acts) -> 
      ctr_recv_st_upd cs2 cs3 ->
      ctr_recv_st_upd cs1 cs3. 


Tactic Notation "dh" ident(E) tactic(tac) :=
  match goal with
  | H: _ |- context [match ?expr with _ => _ end] => 
      destruct expr eqn:E; tac
  end.

Tactic Notation "dc" ident(E) tactic(tac) :=
  match goal with
  | H: _ |- context[if ?expr then _ else _] =>
      destruct expr eqn:E; tac
  end.

Lemma exe_acts_inhabited :
  forall n bs bs', 
    execute_actions n bs true = Ok bs' -> 
    inhabited (ChainTrace bs bs').
Proof.
  introv Hexea.
  lets H_: execute_actions_trace_pb_ Hexea; auto.
Qed.   

Lemma contract_recv_upd_states `{ContractCls}: 
  forall n (cc: @ContractCls) (bs bs': ChainState) (cs cs': @ctr_state cc) (cadr: Address), 
    execute_actions n bs true = Ok bs' ->
    env_contracts bs cadr = Some (ctrCtr: WeakContract) -> 
    @contract_state _ ctr_state Hctr_ser_state bs cadr = Some cs ->
    @contract_state _ ctr_state Hctr_ser_state bs' cadr = Some cs' ->
    @ctr_recv_st_upd cc cs cs'.  
Proof.
  induction n.
  -
    introv Hea Hec Hcst Hcst'.
    simpl in Hea.
    destruct_head Hea Ecsq tryfalse.
    inverts Hea.
    rewrite <- Ecsq in Hcst'.
    simpl in Hcst'. 
    rewrite Hcst in Hcst'. inverts Hcst'.
    apply RcvRefl.
  - 
    introv Hexes Hec Hcst Hcst'.
    simpl in Hexes.
    destruct_head Hexes Ecsq tryfalse.
    + 
      inverts Hexes.
      rewrite <- Ecsq in Hcst'. simpl in Hcst'.
      rewrite Hcst in Hcst'.
      inverts Hcst'.
      apply RcvRefl.
    +
      destruct_head Hexes Eea tryfalse.
      destruct a eqn: Ea.
      destruct act_body eqn: Ebd.
      * simpl in Eea.
        unfolds in Eea.
        destruct_cond Eea Elt tryfalse.
        destruct_cond Eea Egt tryfalse.
        destruct_head Eea Eec tryfalse.
        **
          destruct_head Eea Eecst tryfalse.
          destruct w.
          simpl in Eea.
          destruct (address_eqb_spec to cadr) as [Heq_cadr | Hne_cadr].
          *** 
            subst to.
            rewrite Hec in Eec.
            inverts Eec.
            destruct_head Eea Eroo tryfalse.
            destruct t0. inverts Eea.
            simpl in Hexes.
            destruct_head Eroo Eroo_ tryfalse.
            destruct_head Eroo Ercv tryfalse. 
            match type of Ercv with
              context [error_to_weak_error ?tt] =>
                destruct tt eqn: Ercv_; tryfalse
            end.
            simpl in Ercv.
            inverts Ercv.
            destruct t0. simpl in Eroo. inverts Eroo.
            assert (Hcst_ := Hcst).
            unfolds in Hcst_. simpl in Hcst_.
            destruct_head Hcst_ Eecs tryfalse.
            inverts Eecst.
            rewrite Hcst_ in Eroo_. simpl in Eroo_. inverts Eroo_.
            eapply RcvUpd; eauto.
            lets H__: IHn Hexes; eauto.
            simpl in H__. eapply H__; eauto.
            unfold contract_state, set_contract_state; simpl.
            rewrite address_eq_refl.
            rewrite deserialize_serialize. auto.
          ***
            destruct_head Eea Ewee tryfalse.
            destruct t0.
            inverts Eea.
            simpl in Hexes.
            lets H__: IHn Hexes; eauto.
            simpl in H__.
            eapply H__; eauto.
            unfold set_contract_state, contract_state; simpl.
            asserts_rewrite ((cadr =? to)%address = false).
            { eapply address_eq_ne; eauto. }
            unfolds in Hcst.
            dh Eecs tryfalse. 
            simpl in Hcst. auto.
        **
          destruct_cond Eea Eaic tryfalse.
          inverts Eea.
          simpl in Hexes.
          lets H__: IHn Hexes; eauto.

      *
        simpl in Eea.
        unfold send_or_call in Eea.
        destruct_cond Eea Elt tryfalse.
        destruct_cond Eea Egt tryfalse.
        destruct_head Eea Eec tryfalse.
        ** 
          destruct_head Eea Eecst tryfalse.
          destruct w.
          simpl in Eea.
          destruct (address_eqb_spec to cadr) as [Heq_cadr | Hne_cadr].
          *** 
            subst to.
            rewrite Hec in Eec.
            inverts Eec.
            destruct_head Eea Eroo tryfalse.
            destruct t0. inverts Eea.
            simpl in Hexes.
            destruct_head Eroo Eroo_ tryfalse.
            destruct_head Eroo Emsgs tryfalse. 
            destruct_head Eroo Ercv tryfalse. 
            match type of Ercv with
              context [error_to_weak_error ?tt] =>
                destruct tt eqn: Ercv_; tryfalse
            end.
            simpl in Ercv.
            inverts Ercv.
            destruct t1. simpl in Eroo. inverts Eroo.
            assert (Hcst_ := Hcst).
            unfolds in Hcst_. simpl in Hcst_.
            destruct_head Hcst_ Eecs tryfalse.
            inverts Eecst.
            rewrite Hcst_ in Eroo_. simpl in Eroo_. inverts Eroo_.
            eapply RcvUpd; eauto.
            lets H__: IHn Hexes; eauto.
            simpl in H__. eapply H__; eauto.
            unfold contract_state, set_contract_state; simpl.
            rewrite address_eq_refl.
            rewrite deserialize_serialize. auto.
          ***
            destruct_head Eea Ewee tryfalse.
            destruct t0.
            inverts Eea.
            simpl in Hexes.
            lets H__: IHn Hexes; eauto.
            simpl in H__.
            eapply H__; eauto.
            unfold set_contract_state, contract_state; simpl.
            asserts_rewrite ((cadr =? to)%address = false).
            { eapply address_eq_ne; eauto. }
            unfolds in Hcst.
            dh Eecs tryfalse. 
            simpl in Hcst. auto.
        **
          destruct_head Eea Eaic tryfalse.
      *
        unfolds in Eea.
        unfolds in Eea.
        destruct_cond Eea Elt tryfalse.
        destruct_cond Eea Egt tryfalse.
        destruct_head Eea Egnc tryfalse.
        destruct_head Eea Ecca tryfalse.
        destruct_head Eea Ewi tryfalse.
        inverts Eea.
        assert (Hnea: a0 <> cadr).
        {
          unfolds in Ecca. 
          destruct (address_is_contract a0);
            destruct (isNone (env_contracts bs a0)%bool) eqn: Hn; simpl in Ecca; tryfalse.
          unfolds in Hn.
          introv Hff. subst a0.
          rewrite Hec in Hn. false.
        }                      
        simpl in Hexes.
        lets H__: IHn Hexes; eauto.
        simpl in H__.
        eapply H__; eauto.
        asserts_rewrite ((cadr =? a0)%address = false).
        { eapply address_eq_ne; eauto. }
        auto.
        unfold contract_state, set_contract_state; simpl.
        asserts_rewrite ((cadr =? a0)%address = false).
        { eapply address_eq_ne; eauto. }
        unfolds in Hcst.
        dh Eecs tryfalse.
        auto.
Qed.

(* *)
(* Proof method for strategy-aware liquidity *) 

Class LiqVerif :=
  build_liq_verif { 
      A: Set; 
      Ord: A -> A -> Prop; (* < *) 
      wf_ord: well_founded Ord; 
      trans: forall a1 a2 a3, Ord a1 a2 -> Ord a2 a3 -> Ord a1 a3; 
      Inv: ChainState -> ChainState -> Prop; (* invariant *)
      Var: ChainState -> ChainState -> option A; (* variant *) 

      setup : Type; 
      Hser_setup: Serializable setup; 
      msg: Type; 
      Hser_msg: Serializable msg; 
      state: Type; 
      Hser_state: Serializable state;
      error: Type; 
      Hser_err: Serializable error;

      theCtr: Contract setup msg state error;
      
      cur_adr: Address; 
      inist : ChainState;

      miner_adr: Address;
      H_mnctr : address_not_contract miner_adr = true; 
    }. 

Definition minimal `{LiqVerif} (x : A) : Prop :=
  forall y, ~ Ord y x.

(* base *)
Definition VC_B `{LiqVerif} (phi: ChainState -> ChainState -> Prop) :=  
  forall csref cs a,
    Inv csref cs -> 
    Var csref cs = Some a ->
    minimal a -> 
    phi csref cs. 

(* condition for all reachable chain states *)  
Definition VC_R `{LiqVerif} :=
  forall cs, 
    transition_reachable miner_adr theCtr cur_adr inist cs -> 
    (Inv cs cs /\ Var cs cs <> None). 
    
Definition VC_A `{LiqVerif} (addrs: list Address) (delta_att: strat miner_adr addrs) :=
  forall csref cs cs' (tr: TransitionTrace miner_adr inist cs) (tr': TransitionTrace miner_adr inist cs') a n, 
    Var csref cs = Some a ->
    Inv csref cs ->
    multiStratDrive miner_adr addrs delta_att inist cs tr cs' tr' n -> 
    (Inv csref cs' /\
       (exists a', Var csref cs' = Some a' /\ (~minimal a -> (Ord a' a \/ a' = a)))). 

(* condition for a user step in phase 2 *) 
Definition VC_U `{LiqVerif} (addrs: list Address) (delta_usr: strat miner_adr addrs) :=
  forall csref cs (tr: TransitionTrace miner_adr inist cs) a,
    Inv csref cs ->
    Var csref cs = Some a ->
    ~minimal a -> 
    exists cs',
    exists (tr': TransitionTrace miner_adr inist cs'),
      stratDrive miner_adr addrs delta_usr inist cs tr cs' tr' /\ 
        (Inv csref cs' /\ (exists a', Var csref cs' = Some a' /\ Ord a' a)). 

Definition P `{LiqVerif}: A -> Prop :=
  fun a =>
    forall (cs s_ref : ChainState) (tr : TransitionTrace miner_adr inist cs) (adrs_att : list Address)
           (delta_att : strat miner_adr adrs_att) (adrs_usr : list Address)
           (delta_usr : strat miner_adr adrs_usr) (phi : ChainState -> ChainState -> Prop), 
      Inv s_ref cs ->
      Var s_ref cs = Some a -> 
      VC_A adrs_att delta_att ->
      VC_U adrs_usr delta_usr ->
      VC_B phi ->
      userLiquidates miner_adr adrs_usr delta_usr adrs_att delta_att cur_adr inist cs s_ref tr phi. 

Require Import Coq.Logic.Classical.

Lemma liquidation_if_inv_holds `{LiqVerif}:
  forall a cs s_ref (tr: TransitionTrace miner_adr inist cs) adrs_att delta_att adrs_usr delta_usr phi, 
    Inv s_ref cs -> 
    Var s_ref cs = Some a ->
    VC_A adrs_att delta_att ->
    VC_U adrs_usr delta_usr ->
    VC_B phi ->
    userLiquidates miner_adr adrs_usr delta_usr adrs_att delta_att cur_adr inist cs s_ref tr phi. 
Proof.
  lets H__: well_founded_ind wf_ord P.
  eapply H__; eauto.
  clear H__.
  introv IH.
  unfold P in *.
  introv Hinv (* Hinv_ref *) Hvar (* Hnn *) Hvca Hvcu2 Hvcb.
  assert (Hor: minimal x \/ ~minimal x) by tauto.
  destruct Hor as [Hmin | Hnmin].
  -
    unfolds in Hvcb.
    lets Hvcb_: Hvcb Hinv.
    lets H__: Hvcb_ Hvar Hmin.
    eapply U_Base; eauto.
  -
    assert (Hvcu2_ := Hvcu2).
    unfolds in Hvcu2.
    lets H__: Hvcu2 tr Hinv Hvar Hnmin.
    destruct H__ as (cs' & tr' & Hsd & Hinv' & Hex).
    destruct Hex as (a' & HHa' & Hord').
    eapply U_Step; eauto.
    assert (Hor_: phi s_ref cs' \/ ~phi s_ref cs') by tauto.
    destruct Hor_ as [Hphi | Hnphi].
    +
      eapply E_Base; eauto.
    +
      eapply E_Step; eauto.
      introv Hmsd.
      assert (Hvca2 := Hvca).
      unfolds in Hvca.
      lets H_: Hvca Hmsd; eauto.
      assert (~minimal a').
      {
        assert (Hor: ~minimal a' \/ minimal a') by tauto.
        destruct Hor; auto.
        unfolds in Hvcb.
        lets Hcontra: Hvcb Hinv' HHa'.
        specializes Hcontra; eauto.
      }
      destruct H_ as (Hinv'' & Hex).
      destruct Hex as (a'' & Ha'' & Hord'').
      specializes Hord''; eauto.
      assert (Hord: Ord a'' x).
      {
        destruct Hord''.
        eapply trans; eauto.
        subst.
        auto.
      }
      lets H__: IH Hord Hinv'' Ha'' Hvca2.
      lets H_: H__ Hvcu2_ Hvcb. clear H__.
      eauto.
Qed. 

Lemma interleaved_exe_inv_var `{LiqVerif}: 
  forall adrs_usr delta_usr adrs_att delta_att tr cs_ref tr', 
    VC_R ->  
    is_init_state theCtr cur_adr inist -> 
    interleavedExecution miner_adr adrs_usr delta_usr adrs_att delta_att inist inist tr Tusr cs_ref tr' ->
    Inv cs_ref cs_ref /\ Var cs_ref cs_ref <> None. 
Proof.
  introv Hvcr Hini Hexe.
  assert (Htrc0: transition_reachable miner_adr theCtr cur_adr inist inist).
  {
    eapply transition_reachable_init_state; eauto.
  }
  assert (Htrc: transition_reachable miner_adr theCtr cur_adr inist cs_ref).
  {
    eapply transition_reachable_interleavedExecution_transition_reachable; eauto.
  }
  eapply Hvcr; eauto.
Qed. 
  
Theorem soundness `{LiqVerif}:
  forall adrs_att delta_att adrs_usr delta_usr phi,
    VC_R ->
    VC_B phi -> 
    VC_A adrs_att delta_att ->
    VC_U adrs_usr delta_usr ->
    strategy_aware_liquidity miner_adr adrs_usr delta_usr adrs_att delta_att theCtr cur_adr inist phi. 
Proof.
  introv Hvcr Hvcb Hvca Hvcu.
  unfold strategy_aware_liquidity.
  introv Hinist Hie.
  lets H__: interleaved_exe_inv_var Hvcr Hinist Hie; eauto.
  destruct H__ as (Hinv' & Hvar').
  assert (Hex: exists a', Var s' s' = Some a').
  {
    destruct (Var s' s'); tryfalse; eauto.
  }
  destruct Hex as (a' & Ha').
  lets H__: liquidation_if_inv_holds Hinv' Ha'; eauto.
Qed.


Require Import Automation.
Require Import Lia.

Lemma get_valid_header_is_valid_header `{LiqVerif}:
  forall (s: ChainState), 
    validate_header (get_valid_header miner_adr s) s = true.  
Proof.
  intros.
  unfold get_valid_header.
  unfold validate_header.
  propify.
  repeat split; cbn; try lia; eauto.
  apply H_mnctr.
  unfold miner_reward.
  lia.
Qed.

Lemma trans_rc_env_contracts `{LiqVerif}:
  forall cs,
    is_init_state theCtr cur_adr inist -> 
    transition_reachable miner_adr theCtr cur_adr inist cs ->
    env_contracts cs cur_adr = Some (theCtr:WeakContract). 
Proof.
  introv Hini Htrc_s.  
  eapply transition_reachable_impl_reachable_through in Htrc_s; auto.
  eapply reachable_through_contract_deployed in Htrc_s;eauto.
  unfolds in Hini.
  destructs Hini.
  auto.  
Qed.


(**)
(* Refutation method for strategy-aware liquidity *)  

Class LiqRefut :=
  build_liq_refut { 
      Inv1: ChainState -> ChainState -> Prop; (* invariant *)
      Inv2: ChainState -> ChainState -> Prop; (* invariant *)

      rft_setup : Type; 
      rft_Hser_setup: Serializable rft_setup; 
      rft_msg: Type; 
      rft_Hser_msg: Serializable rft_msg; 
      rft_state: Type; 
      rft_Hser_state: Serializable rft_state;
      rft_error: Type; 
      rft_Hser_err: Serializable rft_error;

      rft_theCtr: Contract rft_setup rft_msg rft_state rft_error;
      
      rft_cur_adr: Address; 
      rft_inist : ChainState;
      Hinit: is_init_state rft_theCtr rft_cur_adr rft_inist;

      rft_miner_adr: Address;
      rft_H_mnctr : address_not_contract rft_miner_adr = true; 
    }. 

(* refutation condition: reachability of state satisfying Inv1 *) 
Definition RC_R `{LiqRefut} adrs_u dlta_usr adrs_a dlta_att :=
  exists (tr: TransitionTrace rft_miner_adr rft_inist rft_inist) cs' tr',   
    interleavedExecution 
      rft_miner_adr adrs_u dlta_usr adrs_a dlta_att rft_inist rft_inist tr Tusr cs' tr' /\ Inv1 cs' cs'.

(* refutation condition for a user step *) 
Definition RC_U `{LiqRefut} adrs_u (dlta_usr: strat rft_miner_adr adrs_u) :=
  forall csref cs (tr: TransitionTrace rft_miner_adr rft_inist cs) cs' tr',  
    Inv1 csref cs -> 
    stratDrive rft_miner_adr adrs_u dlta_usr rft_inist cs tr cs' tr' -> 
    Inv2 csref cs'. 

(* refutation condition for a series of adversary steps *) 
Definition RC_A `{LiqRefut} adrs_a (dlta_att: strat rft_miner_adr adrs_a) :=
  forall csref cs (tr: TransitionTrace rft_miner_adr rft_inist cs), 
    Inv2 csref cs ->
    exists cs' tr' n, 
      multiStratDrive rft_miner_adr adrs_a dlta_att rft_inist cs tr cs' tr' n /\ 
        Inv1 csref cs'.

Definition RC_B `{LiqRefut} (phi: ChainState -> ChainState -> Prop) :=
  forall csref cs, (Inv1 csref cs \/ Inv2 csref cs) -> ~phi csref cs. 

Lemma user_liq_contra `{LiqRefut}:
  forall adrs_usr delta_usr adrs_att delta_att cs_ref phi cs' tr',  
    (
      envProgress rft_miner_adr adrs_usr delta_usr adrs_att delta_att rft_cur_adr rft_inist
        cs' cs_ref tr' phi ->
      (* transition_reachable rft_miner_adr rft_theCtr rft_cur_adr rft_inist cs_ref -> *)
      RC_B phi -> 
      RC_U adrs_usr delta_usr -> 
      RC_A adrs_att delta_att ->     
      Inv2 cs_ref cs' -> 
      False          
    )
    /\ 
      (
        userLiquidates rft_miner_adr adrs_usr delta_usr adrs_att delta_att rft_cur_adr rft_inist
          cs' cs_ref tr' phi ->        
        RC_B phi -> 
        RC_U adrs_usr delta_usr -> 
        RC_A adrs_att delta_att ->     
        Inv1 cs_ref cs' -> 
        False
      ). 
Proof.
  intros.
  lets H__: uliq_mutual_ind rft_miner_adr adrs_usr delta_usr adrs_att delta_att.
  lets H_: H__ rft_cur_adr rft_inist. clear H__.
  lets H__: H_
              (fun (s sref: ChainState)
                   (tr: TransitionTrace rft_miner_adr rft_inist s)
                   (phi: ChainState -> ChainState -> Prop)
                   (ep: envProgress rft_miner_adr adrs_usr delta_usr adrs_att delta_att rft_cur_adr
                          rft_inist s sref tr phi) =>
                 RC_B phi ->
                 RC_U adrs_usr delta_usr ->
                 RC_A adrs_att delta_att ->
                 Inv2 sref s ->
                 False)
              (fun (s sref : ChainState)
                   (tr : TransitionTrace rft_miner_adr rft_inist s)
                   (phi : ChainState -> ChainState -> Prop)
                   (ul: userLiquidates rft_miner_adr adrs_usr delta_usr adrs_att delta_att rft_cur_adr
                          rft_inist s sref tr phi) =>
                 RC_B phi ->
                 RC_U adrs_usr delta_usr ->
                 RC_A adrs_att delta_att ->
                 Inv1 sref s ->
                 False).  
  clear H_.
  eapply H__; eauto; clear H__.
  
  - introv Htt Hphi (* Htrc *) Hrcb Hrcu Hrca Hinv2.
    unfolds in Hrcb.
    eapply Hrcb in Hphi; eauto.
    
  - introv Hnphi Ha Ha' (* Htrc *) Hrcb Hrcu Hrca Hinv2.
    lets H_: Hrca Hinv2. 
    destruct H_ as (cs'0 & tr'0 & n & Hmsd & Hinv).
    eapply Ha'; eauto.

  - introv Htt Hphi (* Htrc *) Hrcb Hrcu Hrca Hinv1.
    unfolds in Hrcb.
    eapply Hrcb in Hphi; eauto.

Qed.

Theorem rft_soundness `{LiqRefut}:
  forall adrs_att (delta_att: strat rft_miner_adr adrs_att) adrs_usr (delta_usr: strat rft_miner_adr adrs_usr) phi,
    RC_R adrs_usr delta_usr adrs_att delta_att ->  
    RC_B phi -> 
    RC_U adrs_usr delta_usr ->
    RC_A adrs_att delta_att ->
    ~ strategy_aware_liquidity
      rft_miner_adr adrs_usr delta_usr adrs_att delta_att rft_theCtr rft_cur_adr rft_inist phi.  
Proof.
  introv Hrcr Hrcb Hrcu Hrca.
  unfold strategy_aware_liquidity.
  apply impl_lem.
  split.
  apply Hinit.
  unfold RC_R in Hrcr.
  destruct Hrcr as (tr & cs' & tr' & Hitl & Hinv1).
  repeat (apply ex_not_not_all; eexists).
  eauto.
  introv Hf.
  eapply user_liq_contra in Hf; eauto.
Qed.   


(**)
(* Further auxiliary lemmas *)   

Lemma get_valid_header_is_valid_header_ `{LiqRefut}:
  forall (s: ChainState), 
    validate_header (get_valid_header rft_miner_adr s) s = true.  
Proof.
  intros.
  unfold get_valid_header.
  unfold validate_header.
  propify.
  repeat split; cbn; try lia; eauto.
  apply rft_H_mnctr.
  unfold miner_reward.
  lia.
Qed.

Lemma trans_rc_env_contracts_ `{LiqRefut}:
  forall cs,
    transition_reachable rft_miner_adr rft_theCtr rft_cur_adr rft_inist cs ->
    env_contracts cs rft_cur_adr = Some (rft_theCtr:WeakContract). 
Proof.
  introv Htrc_s.
  pose proof Hinit as H_ini.
  eapply transition_reachable_impl_reachable_through in Htrc_s; auto.
  eapply reachable_through_contract_deployed in Htrc_s;eauto.
  unfolds in H_ini.
  destructs H_ini.
  auto.  
Qed.
