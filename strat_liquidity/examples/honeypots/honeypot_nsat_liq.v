
Require Import honeypot.

Require Import Lia.

Section Liquidity.
  
  Let h_usr := honeypot.h_usr.
  Let d_usr := honeypot.d_usr.

  Require Coq.NArith.NArith. 
  Require stdpp.countable.
  Local Open Scope Z_scope.

  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Let caddr := honeypot.caddr.
  Let miner := honeypot.miner.

  Definition byte := Z. 
  Variable att_pass : list byte.

  Variable sha3_func : list byte -> list byte.
  Axiom collision_resistance_prop :
    forall p1 p2, sha3_func p1 = sha3_func p2 -> p1 = p2. 
  Hypothesis sha_attpass_neq_zero: sha3_func att_pass <> [0].

  Instance sha : SHA3 := {
      sha3 := sha3_func;
      collision_resistance := collision_resistance_prop; 
    }. 

  Variable s0 : ChainState.
  Hypothesis H_init: is_init_state contract caddr s0.
  Hypothesis H_miner : address_not_contract miner = true.

  Hypothesis h_usr_eoa : address_not_contract h_usr = true.
  Hypothesis d_usr_eoa : address_not_contract d_usr = true.

  Hypothesis addr_neq : h_usr <> d_usr.   

  Definition inv_func (csref cs: ChainState) : Prop :=
    transition_reachable miner contract caddr s0 cs /\ 
      funds cs caddr > 0 /\ 
      exists st,
        contract_state cs caddr = Some st /\ 
          st.(hashPass) = sha3 att_pass /\
          st.(passLocked) = true. 

  Program Instance liqRefut : LiqRefut := {
      Inv1 := inv_func;
      Inv2 := inv_func;

      rft_setup := Setup;
      rft_msg := Msg;  
      rft_state := State;
      rft_error := Error;

      rft_cur_adr := caddr;
      rft_inist := s0;
      rft_theCtr := contract; 

      Hinit := H_init; 

      rft_miner_adr := miner;
      rft_H_mnctr := H_miner; 
    }. 

  Definition attacker_call_SetPass: Action :=
    build_call d_usr caddr 1 (SetPass (sha3 att_pass)).

  Definition attacker_call_LockPass: Action :=
    build_call d_usr caddr 0 (LockPass (sha3 att_pass)).
  
  Definition attacker_strat : (strat miner [d_usr]) :=
    fun s0 (s: ChainState) tr =>
      match @contract_state _ State rft_Hser_state s caddr with
      | Some state =>
          if (eq_bytes_dec state.(hashPass) (sha3 att_pass)) then
            [attacker_call_LockPass] 
          else if (negb state.(passLocked)) then
                 [attacker_call_SetPass]
               else 
                 []
      | None => []
      end.

  Definition user_call_GetGift_with_att_pass (amt: Amount): Action :=
    build_call h_usr caddr amt (GetGift att_pass). 

  Hypothesis only_att_knows_att_pass :
    forall (act: Action) amt msg,
      act.(act_body) = act_call caddr amt msg ->
      result_of_option (deserialize msg) deser_error = Ok (GetGift att_pass) -> 
      (act.(act_origin) = d_usr \/ act.(act_from) = d_usr).  
  
  Definition well_strat (addrs: list Address) (stt: strat miner addrs) :=
    forall a s0 s (tr: TransitionTrace miner s0 s),  
      List.In a (stt s0 s tr) -> List.In a.(act_origin) addrs. 

  Tactic Notation "dc" ident(E) tactic(tac) :=
    match goal with
    | H: _ |- context[if ?expr then _ else _] =>
        destruct expr eqn:E; tac
    end.

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

  Lemma att_setpass_from_init :
    env_account_balances s0 d_usr >= 1 -> 
    exists s',
      transition miner 1 s0 (attacker_call_SetPass) = Ok s' /\
        funds s' caddr > 0 /\ 
        env_account_balances s0 d_usr >= 1 /\ 
        exists cst',
          contract_state s' caddr = Some cst' /\
            cst'.(hashPass) = sha3 att_pass /\
            cst'.(passLocked) = false. 
  Proof.
    introv Heab.
    unfold transition.
    unfold queue_isb_empty.
    pose proof H_init as Hi.
    unfolds in Hi.
    destruct Hi as (Hrc & Hcsq & Hec & Hex).
    destruct Hex as (ctx & stp & stt & Hecs & Hini).
    rewrite Hcsq.
    unfold evaluate_action.
    pose proof get_valid_header_is_valid_header_ as Hvh.
    unfold liqRefut in Hvh; simpl in Hvh. rewrite Hvh.
    unfold attacker_call_SetPass.
    simpl.
    assert (Hec_s := Hec).
    assert (Hd_nc: address_is_contract h_usr = false).
    {
      eapply address_not_contract_negb; eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
    }
    assert(H_dusr_not_EOA : address_is_contract d_usr = false).
    {
      eapply address_not_contract_negb in d_usr_eoa; eauto.
    }
    assert (Hb: env_account_balances s0 h_usr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    assert (Hc: env_account_balances s0 caddr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    asserts_rewrite (address_neqb d_usr d_usr = false).
    { eapply address_neqb_eq; eauto. }
    rewrite H_dusr_not_EOA.
    unfold send_or_call.
    simpl.
    dc Eee tryfalse.
    {
      false. destruct_address_eq; try congruence.
      unfold miner_reward in Eee. lia. lia.
    }
    rewrite Hec_s.
    rewrite Hecs.
    simpl.
    rewrite deserialize_serialize; simpl.
    rewrite deserialize_serialize; simpl.
    unfold setPass.
    simpl in Hini. unfold init in Hini. inverts Hini.
    simpl.
    eexists. split. eauto.    
    split.
    {
      unfold funds in *. simpl.
      destruct_address_eq; try congruence; try lia.
      unfold miner_reward; lia.
    }
    {
      unfold contract_state. simpl.
      rewrite address_eq_refl.
      rewrite deserialize_serialize.
      split; eauto.
    }
  Qed. 

  Lemma att_lockpass :
    forall s cst, 
      transition_reachable miner contract caddr s0 s -> 
      funds s caddr > 0 ->
      contract_state s caddr = Some cst -> 
      cst.(hashPass) = sha3 att_pass -> 
      cst.(passLocked) = false ->  
      exists s',
        transition miner 1 s (attacker_call_LockPass) = Ok s' /\
          funds s' caddr > 0 /\ 
          exists cst',
            contract_state s' caddr = Some cst' /\
              cst'.(hashPass) = sha3 att_pass /\
              cst'.(passLocked) = true. 
  Proof.
    introv Htrc Hfd Hcst Hpss Hplk.
    unfold transition.
    unfold queue_isb_empty.
    pose proof H_init as Hi.
    unfolds in Hi.
    destruct Hi as (Hrc & Hcsq & Hec & Hex).
    destruct Hex as (ctx & stp & stt & Hecs & Hini).
    eapply transition_reachable_queue_is_empty in Htrc as Hqueue_s; eauto.
    rewrite Hqueue_s.
    unfold evaluate_action.
    pose proof get_valid_header_is_valid_header_ as Hvh.
    unfold liqRefut in Hvh; simpl in Hvh. rewrite Hvh.
    unfold attacker_call_SetPass.
    simpl.
    assert (Hec_s := Hec).
    assert (Hectr: env_contracts s caddr = Some (contract:WeakContract)).
    {
      pose proof trans_rc_env_contracts_ as H_. unfold liqRefut in H_; simpl in H_.
      eapply H_; eauto.
    }
    assert(H_dusr_not_EOA : address_is_contract d_usr = false).
    {
      eapply address_not_contract_negb in d_usr_eoa; eauto.
    }
    assert (Hr: reachable s).
    {
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    assert (Hdb: env_account_balances s d_usr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    asserts_rewrite (address_neqb d_usr d_usr = false).
    { eapply address_neqb_eq; eauto. }
    rewrite H_dusr_not_EOA.
    unfold send_or_call.
    simpl.
    dc Eee tryfalse.
    {
      false. destruct_address_eq; try congruence.
      unfold miner_reward in Eee. lia. lia.
    }
    rewrite Hectr.
    unfolds in Hcst.
    destruct (env_contract_states s caddr) eqn: Eecs; tryfalse.
    simpl.
    simpl in Hcst; rewrite Hcst; simpl.
    rewrite deserialize_serialize; simpl.
    unfold lockPass; simpl.
    rewrite Hpss. unfold sha3. unfold liqRefut; simpl.
    destruct (eq_bytes_dec (sha3_func att_pass) (sha3_func att_pass)) eqn: Ed; tryfalse.
    simpl.
    eexists.
    splits; eauto.
    {
      unfold funds in *.
      simpl. 
      destruct_address_eq; try congruence; try lia.
      unfold miner_reward. lia.
      unfold miner_reward. lia. 
    }
    {
      unfold contract_state.
      simpl.
      rewrite address_eq_refl.
      rewrite deserialize_serialize.
      eexists; splits; eauto.
    }
  Qed.

  Lemma att_strat_setpass_from_init :
    env_account_balances s0 d_usr >= 1 -> 
    exists (tr0: TransitionTrace miner s0 s0) s' tr',
      stratDrive miner [d_usr] attacker_strat s0 s0 tr0 s' tr' /\ 
        funds s' caddr > 0 /\ 
        env_account_balances s0 d_usr >= 1 /\ 
        exists cst',
          contract_state s' caddr = Some cst' /\
            cst'.(hashPass) = sha3 att_pass /\
            cst'.(passLocked) = false. 
  Proof.
    introv Heab.
    lets H__: att_setpass_from_init Heab.
    destruct H__ as (s' & Htrans & Hfds & Hevab & Hex).
    do 3 eexists.
    splits; eauto.
    constructors; eauto.
    eexists. exists Htrans.
    splits; eauto.
    unfold attacker_strat; simpl; eauto.
    unfolds in H_init.
    destruct H_init as (Hr & Hcsq & Hec & (ctx & stp & st & Hecs & Hini)).
    unfold contract_state.
    simpl. rewrite Hecs.
    rewrite deserialize_serialize.
    unfold contract in Hini.
    simpl in Hini.
    unfold init in Hini. inverts Hini.
    simpl hashPass.
    pose proof sha_attpass_neq_zero as Hsan.
    dc Eee tryfalse.
    simpl passLocked.
    simpl. left; auto.
    Unshelve.
    constructors.
  Qed.     
  
  Lemma att_strat_lockpass : 
    forall s cst (tr: TransitionTrace miner s0 s), 
      transition_reachable miner contract caddr s0 s -> 
      funds s caddr > 0 ->
      contract_state s caddr = Some cst -> 
      cst.(hashPass) = sha3 att_pass -> 
      cst.(passLocked) = false ->  
      exists s' tr', 
        stratDrive miner [d_usr] attacker_strat s0 s tr s' tr' /\         
        (* transition miner 1 s (attacker_call_LockPass) = Ok s' /\ *)
          funds s' caddr > 0 /\ 
          exists cst',
            contract_state s' caddr = Some cst' /\
              cst'.(hashPass) = sha3 att_pass /\
              cst'.(passLocked) = true. 
  Proof.
    introv Htrc Hfd Hcst Hpss Hlkd.
    lets H__: att_lockpass Htrc Hfd Hcst Hpss Hlkd.
    destruct H__ as (s' & Htrans & Hfd' & Hex').
    do 2 eexists; splits; eauto.
    constructors.
    eexists. exists Htrans.
    splits; eauto.
    unfold attacker_strat; simpl.
    rewrite Hcst.
    rewrite Hpss.
    unfold liqRefut; simpl.
    dc Eee tryfalse. 
    simpl; auto.
  Qed.     

  Lemma caddr_not_husr :
    caddr <> h_usr.
  Proof.
    introv Hf.
    unfolds in H_init.
    destruct H_init as (hrc & Hcsq & Hec & Hex).
    eapply contract_addr_format in Hec; eauto.
    pose proof addr_ctr_neq as HH.
    lets H_: HH Hec h_usr_eoa.
    apply H_.
    auto.
  Qed.     

  Lemma caddr_not_dusr :
    caddr <> d_usr.
  Proof.
    introv Hf.
    unfolds in H_init.
    destruct H_init as (hrc & Hcsq & Hec & Hex).
    eapply contract_addr_format in Hec; eauto.
    pose proof addr_ctr_neq as HH.
    lets H_: HH Hec d_usr_eoa.
    apply H_.
    auto.
  Qed. 

  Lemma caddr_not_mnr :
    caddr <> miner.
    introv Hf.
    unfolds in H_init.
    destruct H_init as (hrc & Hcsq & Hec & Hex).
    eapply contract_addr_format in Hec; eauto.
    pose proof addr_ctr_neq as HH.
    lets H_: HH Hec H_miner.
    apply H_.
    auto.
  Qed.     

  Lemma correct_cadr_not_h_usr: 
    forall s a, 
      correct_contract_addr s a = true ->
      a <> h_usr.
  Proof.
    introv Hcca.
    unfolds in Hcca.
    destruct (address_is_contract a) eqn: E.
    - 
      lets Hf: addr_ctr_diff E h_usr_eoa.
      rewrite <- address_eq_ne' in Hf.
      auto.
    -
      simpl in Hcca. false.
  Qed.

  Lemma correct_cadr_not_d_usr: 
    forall s a, 
      correct_contract_addr s a = true ->
      a <> d_usr.
  Proof.
    introv Hcca.
    unfolds in Hcca.
    destruct (address_is_contract a) eqn: E.
    - 
      lets Hf: addr_ctr_diff E d_usr_eoa.
      rewrite <- address_eq_ne' in Hf.
      auto.
    -
      simpl in Hcca. false.
  Qed.

  Lemma exe_act_post:
    forall (s s': ChainState) cstate (a: Action),
      funds s caddr > 0 -> 
      env_contracts s h_usr = None ->
      env_contracts s d_usr = None ->
      env_contracts s caddr = Some (contract:WeakContract) -> 
      contract_state s caddr = Some cstate -> 
      cstate.(hashPass) = sha3 att_pass ->
      cstate.(passLocked) = true -> 
      execute_action a s = Ok s' ->
      a.(act_origin) = h_usr ->  
      a.(act_from) <> caddr ->
      a.(act_from) <> d_usr -> 
      funds s' caddr > 0 /\ 
        env_contracts s' h_usr = None /\
        env_contracts s' d_usr = None /\
        env_contracts s' caddr = env_contracts s caddr /\
        (forall act,
            List.In act s'.(chain_state_queue) ->
            (act.(act_from) <> caddr /\ act.(act_from) <> d_usr)) /\ 
        exists cs',
          contract_state s' caddr = Some cs' /\
            cs'.(hashPass) = sha3 att_pass /\
            cs'.(passLocked) = true. 
  Proof.
    introv Hfd Hech Hecd Hec Hcst Hpss Hlkd Hexe Horig Hfrm.
    introv Hfrmd.
    pose proof caddr_not_husr as Hcnh.
    pose proof caddr_not_dusr as Hcnd.
    pose proof caddr_not_mnr as Hcnm.

    assert (Horig_: a.(act_origin) <> caddr).
    { introv Hf. destruct Horig; congruence. }

    destruct a eqn: Eact. 
    destruct act_body eqn: Ebdy; 
      simpl in Horig, Hfrm.

    - (* transfer *)
      simpl in Hexe.
      unfold send_or_call in Hexe.
      destruct_cond Hexe Ealt tryfalse.
      destruct_cond Hexe Eagt tryfalse.
      destruct_head Hexe Eec tryfalse.
      + 
        destruct_head Hexe Eecs tryfalse.
        destruct_head Hexe Ercv tryfalse.
        destruct t.
        inverts Hexe.
        unfold funds.
        simpl.
        simpl in Ercv.
        unfold wc_receive in Ercv.
        destruct w.
        simpl in Ercv.
        destruct_address_eq; try subst; try congruence.
        {
          unfold funds in *.
          splits; auto.
          {
            introv Hin. apply in_act_org_frm in Hin.
            destruct Hin as (Ho & Hf).
            rewrite Hf. split; eauto.
          }
          unfold set_contract_state; simpl.
          unfold contract_state; simpl.
          asserts_rewrite ((caddr =? act_from)%address = false).
          { eapply address_eq_ne'; eauto. }
          unfolds in Hcst. simpl in Hcst.
          destruct_head Hcst Eecs_ tryfalse.
          rewrite Hcst.
          eexists; splits; eauto.
        }
        {
          rewrite Hec in Eec.
          inverts Eec.
          destruct_head Ercv Eroo tryfalse.
          simpl in Ercv. inverts Ercv.
          unfolds in Hcst. simpl in Hcst.
          destruct_head Hcst Ecst tryfalse.
          inverts Eecs.
          rewrite Hcst in Eroo. simpl in Eroo. inverts Eroo.
          split. unfold funds in *. lia.
          splits; auto.
          unfold set_contract_state. unfold contract_state. simpl.
          rewrite address_eq_refl.
          rewrite deserialize_serialize.
          eexists; splits; eauto.
        }
        {
          unfold funds in *.
          splits; auto.
          {
            introv Hin.
            apply in_act_org_frm in Hin.
            destruct Hin as (Hao & Haf).
            rewrite Haf.
            split; eauto.
            introv Hf. rewrite Hf in Eec.
            rewrite Hecd in Eec.
            false. 
          }
          unfold set_contract_state; simpl.
          unfold contract_state; simpl.
          asserts_rewrite ((caddr =? to)%address = false).
          { eapply address_eq_ne'; eauto. }
          unfolds in Hcst. simpl in Hcst.
          destruct_head Hcst Eecs_ tryfalse.
          rewrite Hcst.
          eexists; splits; eauto.
        }
      +
        destruct_cond Hexe Eaic tryfalse.
        inverts Hexe.
        unfold funds in *.
        simpl.
        destruct_address_eq; try congruence.
        splits; auto.
        unfold transfer_balance; simpl.
        unfold contract_state; simpl.
        unfolds in Hcst. simpl in Hcst.
        destruct_head Hcst E__ tryfalse.
        rewrite Hcst.
        eexists; splits; eauto.
        
    - (* call *)
      unfold funds in *. 
      simpl in Hexe.
      unfold send_or_call in Hexe.
      destruct_cond Hexe Eamlt tryfalse.
      destruct_cond Hexe Eamgt tryfalse.
      destruct_head Hexe Eec tryfalse.
      destruct_head Hexe Eecs tryfalse.
      destruct_head Hexe Hwete tryfalse.
      simpl in Hwete.
      destruct t.
      + 
        inverts Hexe.
        simpl.
        unfold weak_error_to_error_receive in Hwete.
        unfold wc_receive in Hwete.
        destruct w.
        destruct_address_eq; try congruence.
        {
          splits; auto.
          {
            introv Hin.
            apply in_act_org_frm in Hin.
            destruct Hin as (Hao & Haf).
            rewrite Haf.
            split; auto.
            introv Hf. rewrite Hf in Eec.
            rewrite Hecd in Eec. false.
          }
          unfold set_contract_state.
          unfold transfer_balance.
          unfold contract_state; simpl.
          dc Ee_ tryfalse.
          { eapply address_eq_ne in n0. false. }
          unfolds in Hcst; simpl in Hcst.
          destruct_head Hcst Ecst tryfalse.
          rewrite Hcst.
          eexists; splits; eauto.
        }
        {
          subst.
          rewrite Hec in Eec.
          inverts Eec.
          destruct_head Hwete Eroos tryfalse.
          destruct_head Hwete Eroom tryfalse.
          destruct t0 eqn: Et0; tryfalse.
          -
            unfold setPass in Hwete.
            simpl in Hwete.
            unfolds in Hcst.
            rewrite Eecs in Hcst; simpl in Hcst.
            rewrite Hcst in Eroos.
            simpl in Eroos. inverts Eroos.
            rewrite Hlkd in Hwete.
            simpl in Hwete.
            inverts Hwete.
            splits; eauto.
            lia.
            unfold set_contract_state.
            unfold transfer_balance, contract_state.
            simpl.
            rewrite address_eq_refl.
            rewrite deserialize_serialize.
            eexists; splits; eauto.
          -
            unfold getGift in Hwete.
            simpl in Hwete.
            unfolds in Hcst.
            rewrite Eecs in Hcst; simpl in Hcst.
            rewrite Hcst in Eroos.
            simpl in Eroos. inverts Eroos.
            destruct_head Hwete Erz tryfalse.
            unfold require_zero in Erz; simpl in Erz.
            destruct_cond Erz Eamtz tryfalse.
            destruct_cond Erz Ebeq tryfalse.
            false. 
            pose proof only_att_knows_att_pass as Hoak.
            match type of Hfrmd with
              _ ?a <> _ => specialize (Hoak a amount msg)
            end.
            simpl in Hoak.
            specializes Hoak; eauto.
            rewrite e0 in Hpss.
            apply collision_resistance_prop in Hpss.
            subst pass.
            eauto.
            destruct Hoak as [Hf | Hf].
            + false.
            + simpl in Hfrmd. false.
          -
            unfold lockPass in Hwete.
            unfold require_zero in Hwete.
            simpl in Hwete.
            destruct_head Hwete Eroo tryfalse.
            destruct_cond Eroo Eamtz tryfalse.
            destruct_cond Eroo Eeqb tryfalse.
            destruct t1. simpl in Hwete. inverts Hwete.
            simpl in Eroo. inverts Eroo.
            split. lia.
            splits; auto.
            unfold set_contract_state. unfold transfer_balance.
            unfold contract_state; simpl.
            rewrite address_eq_refl.
            rewrite deserialize_serialize.
            eexists.
            split; eauto.
            simpl. split; auto.
            unfolds in Hcst; simpl in Hcst.
            destruct_head Hcst Eee_ tryfalse.
            inverts Eecs.
            rewrite Hcst in Eroos.
            simpl in Eroos.
            inverts Eroos.
            auto.
        }
        {
          splits; auto.
          {
            introv Hin.
            apply in_act_org_frm in Hin.
            destruct Hin as (Hao & Haf).
            rewrite Haf.
            split; auto.
            introv Hf. rewrite Hf in Eec. rewrite Hecd in Eec. false.
          }
          unfold set_contract_state.
          unfold transfer_balance.
          unfold contract_state; simpl.
          dc Ee_ tryfalse.
          { eapply address_eq_ne in n1. false. }
          unfolds in Hcst; simpl in Hcst.
          destruct_head Hcst Ecst tryfalse.
          rewrite Hcst.
          eexists; splits; eauto.
        }
      +
        simpl in Horig_.
        destruct_cond Hexe E__ tryfalse.
    -
      (* deploy *)
      simpl in Hexe.
      unfold deploy_contract in Hexe.
      destruct_cond Hexe Eamtl tryfalse.
      destruct_cond Hexe Eamtg tryfalse.
      destruct_head Hexe Egnc tryfalse.
      destruct_head Hexe Ecca tryfalse.
      simpl in Hexe.
      unfold wc_init in Hexe.
      destruct c.
      destruct_head Hexe Hinif tryfalse.
      inverts Hexe.
      simpl.
      unfold funds in *.
      simpl.
      destruct_address_eq; try congruence.
      { (* deploy at caddr -- error *) 
        unfolds in Ecca.
        subst.
        assert (Hf: isNone (env_contracts s caddr) = false).
        {
          unfolds. rewrite Hec. auto.
        }
        rewrite Hf in Ecca.
        clear -Ecca.
        destruct (address_is_contract caddr); simpl in Ecca; tryfalse. 
      }
      {
        apply correct_cadr_not_h_usr in Ecca. false.
      }
      {
        apply correct_cadr_not_d_usr in Ecca. false.
      }
      {
        splits; auto.
        unfold contract_state, set_contract_state.
        simpl.
        destruct_address_eq; try congruence.
        unfolds in Hcst.
        destruct (env_contract_states s caddr) eqn: EE; tryfalse.
        simpl in Hcst. rewrite Hcst.
        eexists; splits; eauto.
      }
  Qed.      

  Lemma exe_acts_post:
    forall n (s s': ChainState) cstate,
      funds s caddr > 0 -> 
      env_contracts s h_usr = None ->
      env_contracts s d_usr = None ->
      env_contracts s caddr = Some (contract:WeakContract) -> 
      contract_state s caddr = Some cstate -> 
      cstate.(hashPass) = sha3 att_pass ->
      cstate.(passLocked) = true -> 
      execute_actions n s true = Ok s' -> 
      (forall act,
          List.In act (s.(chain_state_queue)) ->
          act.(act_origin) = h_usr /\ act.(act_from) <> caddr /\ act.(act_from) <> d_usr) -> 
      funds s' caddr > 0 /\ 
        env_contracts s' h_usr = None /\
        env_contracts s' d_usr = None /\ 
        env_contracts s' caddr = env_contracts s caddr /\
        exists cs',
          contract_state s' caddr = Some cs' /\
            cs'.(hashPass) = sha3 att_pass /\
            cs'.(passLocked) = true. 
  Proof.
    induction n;
      introv Hfd Hech Hecd Hecc Hcs Hpss Hlkd Hexe Hacts.
    - 
      simpl in Hexe.
      destruct_head Hexe Ecsq tryfalse.
      inverts Hexe.
      simpl.
      split. unfold funds in *. simpl. auto.
      splits; eauto.
    -
      simpl in Hexe.
      destruct_head Hexe Ecsq tryfalse.
      + 
        inverts Hexe.
        unfold funds in *.
        splits; eauto.
      +
        destruct_head Hexe Ee tryfalse.
        assert (Hacts_ := Hacts).
        specialize (Hacts_ a).
        specializes Hacts_; simpl; auto.
        lets H__: exe_act_post Hfd Hech Hecd Hecc Hcs Hpss.
        lets H_: H__ Hlkd Ee. clear H__.
        destruct Hacts_ as (Hoh & Hfc & Hfd_).
        specializes H_; eauto.
        destruct H_ as (Hfd' & Hech' & Hecd' & Hecc' & Hacts' & Hex).
        destruct Hex as (cs' & Hcst' & Hpass' & Hlkd').
        remember {| chain_state_env := t; chain_state_queue := chain_state_queue t ++ l |} as ss.
        assert (Hfdss: funds ss caddr > 0).
        { subst ss. unfold funds in *. simpl. auto. }
        assert (Hechss: env_contracts ss h_usr = None).
        { subst ss. simpl. auto. }
        assert (Hecdss: env_contracts ss d_usr = None).
        { subst ss. simpl. auto. }        
        assert (Heccss: env_contracts ss caddr = Some (contract: WeakContract)).
        { subst ss. simpl. congruence. }
        assert (Hcstss: contract_state ss caddr = Some cs').
        { subst ss. simpl. congruence. }
        lets H__: IHn Hfdss Hechss Hecdss Heccss Hcstss.
        specialize (H__ Hpass' Hlkd' Hexe).
        specializes H__; eauto.
        {
          introv Hin.
          rewrite Heqss in Hin. simpl in Hin.
          apply in_app_or in Hin.
          destruct Hin as [Hinl | Hinr].
          2: {
            eapply Hacts; eauto.
            simpl; auto.
          }
          lets Hso: exe_act_gen_same_orig Ee; eauto.
          specializes Hso; eauto.
          specializes Hacts'; eauto.
          destruct Hacts'. 
          splits; eauto.
          congruence.
        }
        rewrite Heqss in H__.
        simpl in H__.
        rewrite Hecc' in H__.
        auto.
  Qed.
  
  Lemma exe_husr_trans_post:
    forall (s s':ChainState) cstate (a: Action) n, 
      transition_reachable miner contract caddr s0 s -> 
      env_contracts s caddr = Some (contract:WeakContract) -> 
      funds s caddr > 0 -> 
      contract_state s caddr = Some cstate ->      
      cstate.(hashPass) = sha3 att_pass ->
      cstate.(passLocked) = true -> 
      transition miner n s a = Ok s' -> 
      a.(act_origin) = h_usr -> 
      funds s' caddr > 0 /\ 
        env_contracts s' caddr = env_contracts s caddr /\
        exists cs',
          contract_state s' caddr = Some cs' /\
            cs'.(hashPass) = sha3 att_pass /\
            cs'.(passLocked) = true.             
  Proof.
    introv Htrc Hec Hfd Hcs Hpss Hlkd Htrans Hori.
    pose proof caddr_not_husr as Hcnh.
    pose proof caddr_not_mnr as Hcnm.

    unfold transition in Htrans.
    destruct (queue_isb_empty s) eqn: Eqie; tryfalse.
    destruct_head Htrans Ee tryfalse.
    inverts Htrans.

    unfold evaluate_action in Ee.
    destruct_head Ee Evh tryfalse.
    destruct_head Ee Efonf tryfalse.
    destruct_head Ee Efira tryfalse.
    match type of Ee with
      context [execute_actions _ ?t _ ] => remember t as ss
    end.
    
    assert (Hrcs: reachable s).
    {      
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    assert (Hnh: env_contracts s h_usr = None).
    {
      eapply address_not_contract_not_wc; eauto.
      eapply address_not_contract_negb; eauto.
    }
    assert (Hnd: env_contracts s d_usr = None).
    {
      eapply address_not_contract_not_wc; eauto.
      eapply address_not_contract_negb; eauto.
    }
    lets H__: exe_acts_post ss.
    specializes H__; eauto.
    {
      subst ss. unfold funds in *. simpl.
      destruct_address_eq; try congruence.
    }
    { subst ss. simpl. auto. }
    { subst ss. simpl. auto. }
    { subst ss. simpl. auto. }
    {
      subst ss. simpl.
      unfold add_new_block_to_env. simpl. unfold contract_state. simpl.
      unfolds in Hcs; simpl in Hcs. destruct_head Hcs Eee tryfalse.
      rewrite Hcs. auto.
    }
    {
      introv Hin.
      rewrite Heqss in Hin; simpl in Hin.
      destruct Hin; tryfalse.
      subst act.
      simpl in Efonf.
      destruct_cond Efonf Eeq tryfalse.
      apply address_neqb_eq in Eeq. 
      splits; eauto; try congruence.
    }      
    rewrite Heqss in H__.
    simpl in H__.
    destructs H__.
    splits; eauto.
  Qed.

  Theorem honeypot_unsat_strat_liquidity:
    env_account_balances s0 d_usr >= 1 ->
    forall (hstrat: strat miner [h_usr]),
      well_strat [h_usr] hstrat ->
      ~strat_liquidity miner [h_usr] hstrat [d_usr] attacker_strat contract caddr s0.  
  Proof.
    introv Heab Hws.
    rewrite <- strat_liq_inst.
    assert (Htrc0: transition_reachable miner contract caddr s0 s0).
    {
      eapply transition_reachable_init_state; eauto.
    }
    lets H__: rft_soundness; eauto.
    eapply H__; eauto; clear H__.
    {
      unfolds.
      unfold liqRefut; simpl.
      lets Hs1: att_strat_setpass_from_init Heab; eauto. 
      destruct Hs1 as (tr0 & s1 & tr1 & Hsd1 & Hfd1 & Heab1 & Hex).
      destruct Hex as (cst1 & Hcst1 & Hpss1 & Hplkd1).
      assert (Htrc1: transition_reachable miner contract caddr s0 s1).
      { 
        eapply transition_reachable_trans; eauto.
      }
      lets Hs2: att_strat_lockpass tr1 Htrc1 Hfd1 Hcst1.
      specializes Hs2; eauto.
      destruct Hs2 as (s2 & tr2 & Hsd2 & Hfd2 & Hex).
      destruct Hex as (cst2 & Hcst2 & Hpss2 & Hplkd2).
      exists tr0 s2 tr2.
      split.
      eapply ISE_Step; eauto.
      eapply IS_Refl; eauto.
      eapply MS_Step; eauto.
      eapply MS_Step; eauto.
      eapply MS_Refl; eauto.

      unfold inv_func.
      splits; eauto.
      eapply transition_reachable_trans in Htrc0; eauto.
    }
    {
      unfolds.
      introv Hinvor.
      unfold Inv1, Inv2 in Hinvor.
      unfold liqRefut in Hinvor.
      assert (Hif: inv_func csref cs) by tauto.
      clear Hinvor.
      unfold inv_func in Hif.
      destructs Hif.
      lia.
    }
    {
      unfolds.
      introv Hinv1 Hsd.
      unfolds in Hinv1. unfold liqRefut in Hinv1; simpl in Hinv1.
      unfolds in Hinv1.
      destruct Hinv1 as (Htrc & Hfd & Hex).
      destruct Hex as (st & Hcst & Hpss & Hlkd).
      unfold stratDrive in Hsd.
      destruct Hsd as (a & n & Htrans & Hin & Htr').
      unfold liqRefut in Htrans; simpl in Htrans.
      lets H__: exe_husr_trans_post Htrc.
      pose proof trans_rc_env_contracts_ cs as Hte.
      unfold liqRefut in Hte; simpl in Hte.
      specialize (Hte Htrc).
      specialize (H__ Hte).
      specialize (H__ Hfd Hcst Hpss Hlkd Htrans).
      unfolds in Hws.
      unfold liqRefut in Hin; simpl in Hin.
      specializes Hws; eauto.
      simpl in Hws.
      destruct Hws as [Heq_ | Hf]; tryfalse.
      rewrite Heq_ in H__.
      specializes H__; eauto.
      destruct H__ as (Hfd' & Hec' & Hex).
      unfolds. unfold liqRefut; simpl.
      unfolds.
      split.
      eapply transition_reachable_transition_transition_reachable; eauto.
      splits; eauto.
    }
    {
      unfolds.
      introv Hinv2.
      unfolds in Hinv2.
      unfold liqRefut in Hinv2; simpl in Hinv2.
      unfold Inv1. unfold liqRefut; simpl.
      do 3 eexists; splits; eauto.
      eapply MS_Refl; eauto.
    }
  Qed.
  
End Liquidity.
