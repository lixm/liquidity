
Require Import funds_management_err.

Require Import Lia.

Section Liquidity.
  
  Let h_usr := funds_management_err.h_usr.
  Let d_usr := funds_management_err.d_usr.
  Let adm := funds_management_err.adm. 

  Require Coq.NArith.NArith. 
  Require stdpp.countable.
  Local Open Scope Z_scope.

  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Let caddr := funds_management_err.caddr.
  Let miner := funds_management_err.miner.

  Variable s0 : ChainState.
  Hypothesis H_init: is_init_state contract caddr s0.
  Hypothesis H_miner : address_not_contract miner = true.

  Hypothesis h_usr_eoa : address_not_contract h_usr = true.
  Hypothesis d_usr_eoa : address_not_contract d_usr = true.
  Hypothesis adm_eoa : address_not_contract adm = true.

  Hypothesis addr_neq : adm <> h_usr /\ adm <> d_usr /\ h_usr <> d_usr.   

  Definition inv1_func (csref cs: ChainState) : Prop :=
    transition_reachable miner contract caddr s0 cs /\ 
      funds cs caddr > 0 /\ 
      exists st,
        contract_state cs caddr = Some st /\ 
          st.(status) = FMap.empty.  

  Definition inv2_func (csref cs: ChainState) : Prop :=
    transition_reachable miner contract caddr s0 cs /\ 
      funds cs caddr > 0 /\ 
      exists st,
        contract_state cs caddr = Some st /\ 
          (FMap.find h_usr st.(status) = Some status_requested \/ 
             FMap.find h_usr st.(status) = None) /\
          (FMap.find adm st.(status) = Some status_requested \/ 
             FMap.find adm st.(status) = None) /\
          (forall adr,
              address_neqb adr h_usr = true ->
              address_neqb adr adm = true ->
              FMap.find adr st.(status) = None). 
  
  Program Instance liqRefut : LiqRefut := {
      Inv1 := inv1_func;
      Inv2 := inv2_func;

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

  Definition attacker_call_reinit: Action :=
    build_call d_usr caddr 0 ReInit. 

  Definition attacker_strat : (strat miner [d_usr]) :=
    fun s0 (s: ChainState) tr =>
      match @contract_state _ State rft_Hser_state s caddr with
      | Some state =>
          match FMap.find h_usr state.(status) with
            Some b =>
              if (b =? status_requested)%nat then [attacker_call_reinit] else []
          | None =>
              match FMap.find adm state.(status) with
                Some b =>
                  if (b =? status_requested)%nat then [attacker_call_reinit] else []
              | None => []
              end                  
          end
      | _ => []
      end.
  
  Definition usr_deposit: Action :=
    build_transfer h_usr caddr 1.

  Definition usr_may_deposit (hstrat: strat miner [h_usr; adm]) :=
    forall s tr, List.In usr_deposit (hstrat s0 s tr).
  
  Lemma ex_user_deposit_pos_bal:
    env_account_balances s0 h_usr >= 1 -> 
    exists s',
      transition miner 1 s0 (usr_deposit) = Ok s' /\
        funds s' caddr > 0 /\ 
        exists cst',
          contract_state s' caddr = Some cst' /\
            cst'.(status) = FMap.empty /\
            cst'.(admin) = adm.
  Proof.
    introv Hbal.
    unfold transition.
    unfold queue_isb_empty.
    pose proof H_init as Hi.
    unfolds in Hi.
    destruct Hi as (Hrc & Hcsq & Hec & Hex).
    rewrite Hcsq.
    unfold evaluate_action.
    pose proof get_valid_header_is_valid_header_ as Hvh.
    unfold liqRefut in Hvh; simpl in Hvh. rewrite Hvh.
    unfold usr_deposit.
    simpl.
    destruct_address_eq;try congruence.
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
    assert (Hb: env_account_balances s0 h_usr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    assert (Hc: env_account_balances s0 caddr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    rewrite Hd_nc.
    unfold send_or_call.
    simpl.
    destruct Hex as (ctx & stp & st & Hcst & Hires).
    destruct_address_eq;try congruence.
    {
      assert (Hgtf: (1 >? miner_reward + env_account_balances s0 h_usr) = false).
      { unfold miner_reward. lia. }
      rewrite Hgtf.
      simpl.
      rewrite Hec_s.
      rewrite Hcst.
      simpl.
      rewrite deserialize_serialize.
      simpl.
      unfold receivef.
      simpl.
      rewrite address_eq_refl.
      simpl. 
      eexists. split. eauto.
      split.
      unfold funds in *.
      simpl.
      destruct_address_eq; try congruence; try lia.
      unfold contract_state; simpl.
      rewrite address_eq_refl.
      rewrite deserialize_serialize.
      unfold Blockchain.init in Hires.
      unfold contract in Hires.
      unfold initf in Hires.
      inverts Hires.
      eexists. splits; simpl; eauto.
    }
    {
      lets H__: addr_ctr_neq H_caddr_not_EOA H_miner; eauto; tryfalse. 
    }
    {
      assert (Hf: (1 >? env_account_balances s0 h_usr) = false).
      { lia. }
      rewrite Hf.
      simpl.
      rewrite Hec.
      rewrite Hcst.
      simpl.
      rewrite deserialize_serialize.
      simpl.
      unfold receivef.
      simpl.
      rewrite address_eq_refl.
      simpl. 
      eexists. split. eauto.
      split.
      unfold funds in *.
      simpl.
      destruct_address_eq; try congruence; try lia.
      unfold contract_state; simpl.
      rewrite address_eq_refl.
      rewrite deserialize_serialize.
      unfold Blockchain.init in Hires.
      unfold contract in Hires.
      unfold initf in Hires.
      inverts Hires.
      eexists. splits; eauto.
    }
  Qed.

  Lemma ex_user_strat_deposit_pos_bal:
    forall hstrat, 
      env_account_balances s0 h_usr >= 1 -> 
      usr_may_deposit hstrat -> 
      exists (tr0: TransitionTrace miner s0 s0) s' tr',
        stratDrive miner [h_usr; adm] hstrat s0 s0 tr0 s' tr' /\ 
          funds s' caddr > 0 /\           
          exists cst',
            contract_state s' caddr = Some cst' /\
              cst'.(status) = FMap.empty /\
              cst'.(admin) = adm.
  Proof.
    introv Hbal Hmdp.
    lets H__: ex_user_deposit_pos_bal Hbal.
    destruct H__ as (s' & Htrans & Hex).
    destruct Hex as (cst' & Hcst' & Hemp & Hadm).
    do 3 eexists.
    split.
    constructors. eexists. exists Htrans.
    split; eauto.
    split; eauto.
    Unshelve.
    constructors.
  Qed. 

  Lemma ie_empmap_funds:
    forall (hstrat: strat miner [h_usr; adm]),
      env_account_balances s0 h_usr >= 1 -> 
      usr_may_deposit hstrat ->       
      exists tr s tr' cstate,
        interleavedExecution miner [h_usr; adm] hstrat [d_usr] attacker_strat s0 s0 tr Tusr s tr' /\
          contract_state s caddr = Some cstate /\
          cstate.(status) = FMap.empty /\
          funds s caddr > 0.
  Proof.
    introv Heab Humd.
    lets H__: ex_user_strat_deposit_pos_bal Heab Humd.
    destruct H__ as (tr0 & s' & tr' & Hsd & Hfd & Hex).
    destruct Hex as (cst' & Hcst' & Hemp & Hadm').
    exists tr0 s' tr' cst'.
    split.
    eapply ISE_Step.
    2: { eapply MS_Refl; eauto. }
    eapply ISU_Step; eauto.
    constructors.
    splits; eauto.
  Qed.     
    
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

  Lemma exe_acts_from_empque:
    forall n s b s', 
      execute_actions n s b = Ok s' ->
      s.(chain_state_queue) = [] ->
      s' = s. 
  Proof.
    introv Hea Hemp.
    destruct n.
    -
      simpl in Hea.
      rewrite Hemp in Hea.
      inverts Hea.
      destruct s.          
      simpl in Hemp.
      simpl.
      congruence.
    -
      simpl in Hea.
      rewrite Hemp in Hea.
      inverts Hea.
      destruct s.
      simpl in Hemp.
      simpl.
      congruence.
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

  Lemma caddr_not_adm :
    caddr <> adm.
  Proof.
    introv Hf.
    unfolds in H_init.
    destruct H_init as (hrc & Hcsq & Hec & Hex).
    eapply contract_addr_format in Hec; eauto.
    pose proof addr_ctr_neq as HH.
    lets H_: HH Hec adm_eoa.
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

  Lemma env_contracts_add_block: 
    forall s adr ctr, 
      env_contracts s adr = Some (ctr: WeakContract) -> 
      env_contracts (add_new_block_to_env (get_valid_header miner s) s) adr = Some (ctr: WeakContract). 
  Proof.
    introv Hec.
    unfold add_new_block_to_env.
    simpl.
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

  Lemma correct_cadr_not_adm: 
    forall s a, 
      correct_contract_addr s a = true ->
      a <> adm.
  Proof.
    introv Hcca.
    unfolds in Hcca.
    destruct (address_is_contract a) eqn: E.
    - 
      lets Hf: addr_ctr_diff E adm_eoa.
      rewrite <- address_eq_ne' in Hf.
      auto.
    -
      simpl in Hcca. false.
  Qed.

  Lemma exe_act_post:
    forall (s s': ChainState) cstate (a: Action)
           (Hec_s: env_contracts s caddr = Some (contract:WeakContract)),
      funds s caddr > 0 -> 
      env_contracts s h_usr = None ->
      env_contracts s adm = None -> 
      contract_state s caddr = Some cstate ->      
      (FMap.find h_usr cstate.(status) = None \/  
         FMap.find h_usr cstate.(status) = Some status_requested /\
           (a.(act_from) = a.(act_origin) -> a.(act_from) <> cstate.(admin))) ->
      (FMap.find adm cstate.(status) = None \/  
         FMap.find adm cstate.(status) = Some status_requested /\
           (a.(act_from) = a.(act_origin) -> a.(act_from) <> cstate.(admin))) ->  
      (forall a,
          address_neqb a h_usr = true ->
          address_neqb a adm = true ->
          FMap.find a cstate.(status) = None) -> 
      execute_action a s = Ok s' ->
      (a.(act_origin) = h_usr \/ a.(act_origin) = adm) ->  
      (* a.(act_origin) <> caddr -> *)
      a.(act_from) <> caddr ->
      funds s' caddr > 0 /\ 
      env_contracts s' h_usr = None /\
      env_contracts s' adm = None /\ 
        env_contracts s' caddr = env_contracts s caddr /\
        exists cs',
          contract_state s' caddr = Some cs' /\
            (FMap.find h_usr cs'.(status) = Some status_requested (* /\ chain_state_queue s' = [] *) \/
               FMap.find h_usr cs'.(status) = None) /\ 
            (FMap.find adm cs'.(status) = Some status_requested (* /\ chain_state_queue s' = [] *) \/
               FMap.find adm cs'.(status) = None) /\ 
            (forall a,
                address_neqb a h_usr = true ->
                address_neqb a adm = true -> 
                FMap.find a cs'.(status) = None) /\
            (forall act,
                In act s'.(chain_state_queue) ->
                act.(act_from) <> caddr /\ act.(act_from) <> act.(act_origin)).
  Proof.
    intros * Hec_s Hfd Hnh Hna Hcs Hfmp_h Hfmp_a Hfmpn Hexe Horig Hfrm.
    pose proof caddr_not_husr as Hcnh.
    pose proof caddr_not_adm as Hcna.
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
      destruct_head Hexe Eecs tryfalse.
      destruct_head Hexe Ercv tryfalse.
      destruct t.
      inverts Hexe.
      unfold funds.
      simpl.
      simpl in Ercv.
      unfold wc_receive in Ercv.
      destruct_address_eq; (subst; try congruence; tryfalse).      
      {
        destruct w.
        split.
        unfold funds in *.
        lia.
        split; auto.
        split; auto.
        split; auto.
        unfold contract_state. unfold set_contract_state. simpl.
        destruct_address_eq; try congruence.
        unfolds in Hcs.
        destruct (env_contract_states s caddr) eqn: Eecs_; tryfalse.
        simpl in Hcs.
        rewrite Hcs.
        eexists; splits; eauto.
        simpl in Hfmp_a, Hfmp_h.
        destruct Hfmp_h as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        destruct Hfmp_a as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        introv Hin.
        eapply in_act_org_frm in Hin.
        split.
        destruct Hin; congruence.
        assert (Hne1: act_from <> h_usr).
        { introv Hf. subst. false. }
        assert (Hne2: act_from <> adm).
        { introv Hf. subst. false. }
        destruct Hin; destruct Horig; subst; congruence.
      }
      {
        rewrite Hec_s in Eec.
        inverts Eec.
        simpl in Ercv.
        destruct_head Ercv Eroo tryfalse. 
        destruct_head Ercv Ewe tryfalse.
        unfold receivef in Ewe. simpl in Ewe.
        destruct_cond Ewe Eeq (try congruence; tryfalse).
        simpl in Ewe. inverts Ewe.
        simpl in Ercv.
        inverts Ercv.
        split.
        unfold funds in *.
        lia.
        split; auto.
        split; auto.
        split; auto.
        unfold contract_state, set_contract_state.
        simpl.
        rewrite address_eq_refl.
        rewrite deserialize_serialize.        
        unfolds in Eroo.
        destruct_head Eroo Eds tryfalse.
        inverts Eroo.
        unfold contract_state in Hcs.
        rewrite Eecs in Hcs.
        simpl in Hcs.
        rewrite Hcs in Eds.
        inverts Eds.
        eexists; splits; eauto.
        simpl in Hfmp_a, Hfmp_h.
        destruct Hfmp_h as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        destruct Hfmp_a as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
      }
      {
        destruct w.
        split.
        unfold funds in *.
        lia.
        split; auto.
        split; auto.
        split; auto.
        unfold contract_state. unfold set_contract_state. simpl.
        destruct_address_eq; try congruence.
        unfolds in Hcs.
        destruct (env_contract_states s caddr) eqn: Eecs_; tryfalse.
        simpl in Hcs.
        rewrite Hcs.
        eexists; splits; eauto.
        simpl in Hfmp_a, Hfmp_h.
        destruct Hfmp_h as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        destruct Hfmp_a as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        introv Hin. eapply in_act_org_frm in Hin; eauto.
        split.
        - destruct Hin; congruence.
        - assert (Hne1: to <> h_usr). { introv Hf; subst; tryfalse. }
          assert (Hne2: to <> adm). { introv Hf; subst; tryfalse. }
          destruct Hin; destruct Horig; congruence.
      }
      {
        destruct_cond Hexe Haic tryfalse.
        inverts Hexe.
        unfold funds in *.
        simpl.
        destruct_address_eq; try congruence.
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        unfold contract_state. simpl.
        unfolds in Hcs.
        destruct (env_contract_states s caddr) eqn: EE; tryfalse.
        simpl in Hcs. rewrite Hcs.
        eexists; splits; eauto.
        simpl in Hfmp_a, Hfmp_h.
        destruct Hfmp_h as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        destruct Hfmp_a as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.   
      }

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
      inverts Hexe.
      simpl.
      unfold weak_error_to_error_receive in Hwete.
      unfold wc_receive in Hwete.
      destruct w.
      destruct_address_eq; try congruence; (try subst; tryfalse).
      {
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        unfold contract_state.
        unfold env_contract_states.
        simpl.
        apply address_eq_ne' in n.
        rewrite n.
        unfolds in Hcs.
        destruct (env_contract_states s caddr) eqn: Eecs_; tryfalse.
        simpl in Hcs.
        rewrite Hcs.
        eexists; splits; eauto.
        simpl in Hfmp_a, Hfmp_h.
        destruct Hfmp_h as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        destruct Hfmp_a as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        introv Hin. eapply in_act_org_frm in Hin; eauto.
        split.
        - destruct Hin; congruence.        
        - assert (Hne1: act_from <> h_usr). { introv Hf; subst; tryfalse. }
          assert (Hne2: act_from <> adm). { introv Hf; subst; tryfalse. }
          destruct Hin; destruct Horig; congruence.
      }
      {
        rewrite Hec_s in Eec.
        inverts Eec.
        destruct_head Hwete Eroo tryfalse.
        destruct_head Hwete Emsg tryfalse.
        destruct_head Hwete Eer tryfalse.
        unfold receivef in Eer.
        destruct_address_eq; try congruence; tryfalse. 
        simpl in e0; subst.
        
        unfolds in Hcs.
        rewrite Eecs in Hcs.
        simpl in Hcs.
        rewrite Hcs in Eroo.
        simpl in Eroo.
        inverts Eroo. 
        
        destruct t0.
        - 
          unfold reqWithdrawal in Eer.
          simpl in Eer.
          destruct_cond Eer Eane tryfalse.
          destruct_head Eer Efd tryfalse.
          simpl in Eer. inverts Eer.
          simpl in Hwete.
          inverts Hwete.
          split. lia.
          split; auto.
          split; auto.
          split; auto.
          unfold contract_state. simpl.
          rewrite address_eq_refl.
          rewrite deserialize_serialize.
          eexists.
          split. eauto.
          simpl.
          splits.
          +
            destruct Horig; subst.
            * left. eauto.
            *
              pose proof addr_neq as Han_.
              assert (h_usr <> adm).
              {
                destructs Han_; apply not_eq_sym. auto.
              }
              destruct Hfmp_h as [Hl | (Hr1 & Hr2)].
              right. rewrite <- Hl. eauto.
              left. rewrite <- Hr1. eauto.
          +
            lets Hor: address_eqb_spec adm h_usr.
            inversion Hor as [Heq | Hne].
            *  left. destruct Horig; subst; rewrite Heq; eauto.
            * 
              simpl in Hfmp_a.
              destruct Hfmp_a as [Hl | (Hr1 & Hr2)].
              **
                destruct Horig; subst.
                right. rewrite <- Hl. eauto.
                left. eauto.
              **
                destruct Horig; subst.
                left. rewrite <- Hr1. eauto.
                left. eauto.
          +
            introv Hne1 Hne2.
            simpl in Horig_.
            lets Hor: address_eqb_spec a h_usr.
            destruct Hor as [Heq | Hne].
            * 
              unfolds in Hne1.
              rewrite <- Heq in Hne1.
              rewrite address_eq_refl in Hne1.
              simpl in Hne1; false.
            *
              specializes Hfmpn; eauto.
              destruct Horig; subst.
              ** rewrite <- Hfmpn. eauto.
              ** apply adr_neq_reflect in Hne2. rewrite <- Hfmpn. eauto.
          +
            introv Hf. false. 
        -
          unfold processReq in Eer.
          simpl in Eer.
          destruct_head Eer Efd tryfalse.
          destruct_cond Eer Eane tryfalse.
          assert (Heq: act_from = admin t /\ n1 = status_requested).
          {
            match type of Eane with
              ?e1 && ?e2 = true =>
                destruct e1 eqn: E1_; destruct e2 eqn: E2_;
                simpl in Eane; tryfalse
            end.
            destruct (address_eqb_spec act_from (admin t));
              destruct (Nat.eqb_spec n1 status_requested);
              subst; tryfalse; try (split; congruence).
          }
          destruct Heq; subst.
          simpl in Hfmp_a, Hfmp_h.
          destruct Hfmp_a as [Hfmp_a | (Hr1 & Hr2)]; [ | specializes Hr2; eauto; false].
          destruct Hfmp_h as [Hfmp_h | (Hr1 & Hr2)]; [ | specializes Hr2; eauto; false].
          assert (Hor: a = h_usr \/ a = adm).
          {
            destruct (address_neqb a h_usr) eqn: En1;
              destruct (address_neqb a adm) eqn: En2; tryfalse. 
            specializes Hfmpn; eauto.
            rewrite Efd in Hfmpn. false.
            right. eapply address_neqb_eq; eauto.
            left. eapply address_neqb_eq; eauto.
            left. eapply address_neqb_eq; eauto.
          }
          destruct Hor as [Heqa | Heqa]; subst; false.
        -
          unfold withdraw in Eer.
          simpl in Eer.
          destruct_head Eer Efd tryfalse.
          destruct_cond Eer Eapr tryfalse.
          apply EqNat.beq_nat_true_stt in Eapr.
          subst n1.
          simpl in Hfmp_a, Hfmp_h.
          destruct Horig; subst act_from.
          + rewrite Efd in Hfmp_h.
            destruct Hfmp_h as [Hl | Hr]; [tryfalse | destructs Hr; tryfalse].
          + rewrite Efd in Hfmp_a.
            destruct Hfmp_a as [Hl | Hr]; [tryfalse | destructs Hr; tryfalse].
        -
          unfold reinit in Eer.
          simpl in Eer.
          inverts Eer.
          simpl in Hfmp_a, Hfmp_h.
          split. lia.
          split; auto.
          split; auto.
          split; auto.
          unfold contract_state. simpl.
          destruct_address_eq; try congruence.
          simpl in Hwete.
          inverts Hwete.
          rewrite deserialize_serialize.
          eexists. split. eauto.
          simpl.
          split. right. eauto. split. right. eauto.
          split. intros. eauto.
          introv Hf. false. 
      }
      {
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        unfold contract_state.
        unfold env_contract_states.
        simpl.
        apply address_eq_ne' in n1.
        rewrite n1.
        unfolds in Hcs.
        destruct (env_contract_states s caddr) eqn: Eecs_; tryfalse.
        simpl in Hcs.
        rewrite Hcs.
        eexists; splits; eauto.
        simpl in Hfmp_a, Hfmp_h.
        destruct Hfmp_h as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        destruct Hfmp_a as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        introv Hin. eapply in_act_org_frm in Hin; eauto.
        split.
        -
          rewrite <- address_eq_ne' in n1.
          destruct Hin; congruence.
        -
          assert (Hne1: to <> h_usr). { introv Hf; subst; tryfalse. }
          assert (Hne2: to <> adm). { introv Hf; subst; tryfalse. }
          destruct Hin; destruct Horig; congruence.
      }
      {
        destruct_cond Hexe Hf tryfalse.
      }

    - (* deploy *)
      simpl in Hexe.
      unfold deploy_contract in Hexe.
      destruct_cond Hexe Halt_ tryfalse.
      destruct_cond Hexe Hagt_ tryfalse. 
      destruct_head Hexe Hnwadr tryfalse.
      destruct_cond Hexe Hcca tryfalse.
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
        unfolds in Hcca.
        subst.
        assert (Hf: isNone (env_contracts s caddr) = false).
        {
          unfolds. rewrite Hec_s. auto.
        }
        rewrite Hf in Hcca.
        clear -Hcca.
        destruct (address_is_contract caddr); simpl in Hcca; tryfalse. 
      }
      {
        destructs addr_neq.
        tryfalse.
      }
      {
        apply correct_cadr_not_h_usr in Hcca. false.
      }
      {
        apply correct_cadr_not_adm in Hcca. false.
      }
      {
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        unfold contract_state, set_contract_state.
        simpl.
        destruct_address_eq; try congruence.
        unfolds in Hcs.
        destruct (env_contract_states s caddr) eqn: EE; tryfalse.
        simpl in Hcs. rewrite Hcs.
        eexists; splits; eauto.
        simpl in Hfmp_h.
        destruct Hfmp_h as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.
        destruct Hfmp_a as [Hl | (Hr1 & Hr2)]. right; auto. left; auto.        
      }
      
  Qed. 

  Lemma exe_acts_post:
    forall n (s s': ChainState) cstate, 
      env_contracts s caddr = Some (contract:WeakContract) -> 
      funds s caddr > 0 -> 
      env_contracts s h_usr = None ->
      env_contracts s adm = None -> 
      contract_state s caddr = Some cstate ->      
      (FMap.find h_usr cstate.(status) = None \/  
         FMap.find h_usr cstate.(status) = Some status_requested) ->
      (FMap.find adm cstate.(status) = None \/  
         FMap.find adm cstate.(status) = Some status_requested) ->  
      (forall a,
          address_neqb a h_usr = true ->
          address_neqb a adm = true ->
          FMap.find a cstate.(status) = None) -> 
      execute_actions n s true = Ok s' -> 
      (forall act,
          List.In act s.(chain_state_queue) ->
          (act.(act_origin) = h_usr \/ act.(act_origin) = adm) /\ act.(act_from) <> caddr /\ 
            (FMap.find h_usr cstate.(status) <> None -> act.(act_from) = act.(act_origin) -> act.(act_from) <> cstate.(admin)) /\ 
            (FMap.find adm cstate.(status) <> None -> act.(act_from) = act.(act_origin) -> act.(act_from) <> cstate.(admin))) ->
        (forall act,
            List.In act (tail (s.(chain_state_queue))) -> act.(act_from) <> act.(act_origin))
        ->
        funds s' caddr > 0 /\ 
          env_contracts s' caddr = env_contracts s caddr /\
          exists cs',
            contract_state s' caddr = Some cs' /\
              (FMap.find h_usr cs'.(status) = None \/
                 FMap.find h_usr cs'.(status) = Some status_requested) /\ 
              (FMap.find adm cs'.(status) = None \/
                 FMap.find adm cs'.(status) = Some status_requested) /\  
              (forall a,
                  address_neqb a h_usr = true ->
                  address_neqb a adm = true -> 
                  FMap.find a cs'.(status) = None). 
  Proof.
    induction n;
      introv Hec Hfd Hech Heca Hcs Hfmp_h Hfmp_a Hfmpn Hexe Hacts; introv Htl.
    - 
      simpl in Hexe.
      destruct_head Hexe Ecsq tryfalse.
      inverts Hexe.
      simpl.
      split. unfold funds in *. simpl. auto.
      split; eauto.
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
        destruct Hacts_ as (Horig & Hfrm & Hanh & Hana).
        assert (Hfmp_h_:
                FMap.find h_usr (status cstate) = None \/
                  FMap.find h_usr (status cstate) = Some status_requested /\
                    (a.(act_from) = a.(act_origin) -> a.(act_from) <> cstate.(admin))).
        {
          clear -Hfmp_h Hanh. tauto.
        }
        assert (Hfmp_a_:
                FMap.find adm (status cstate) = None \/
                  FMap.find adm (status cstate) = Some status_requested /\
                    (a.(act_from) = a.(act_origin) -> a.(act_from) <> cstate.(admin))).
        {
          clear -Hfmp_a Hana. tauto.
        }
        lets H__: exe_act_post Hfd Hech Heca Hcs Hfmp_h_ Hfmp_a_; eauto.        
        lets H_: H__ Hfmpn Ee Horig Hfrm. clear H__.
        remember ({| chain_state_env := t; chain_state_queue := chain_state_queue t ++ l |}) as ss.
        destruct H_ as (Hfd_ & Hech_ & Heca_ & Hec_ & Hex_).
        destruct Hex_ as (cs_ & Hcs_ & Hfmp_h__ & Hfmp_a__ & Hfmpn_ & Hacts_).
        rewrite Hec in Hec_.
        assert (Hec_ss: env_contracts ss caddr = Some (contract: WeakContract)).
        {
          subst ss. simpl. auto.
        }
        assert (Hfd_ss: funds ss caddr > 0).
        {
          subst ss. unfold funds in *. simpl. auto.
        }
        assert (Hcs_ss: contract_state ss caddr = Some cs_).
        {
          subst ss. simpl. auto.
        }
        assert (Hech_ss: env_contracts ss h_usr = None).
        { subst ss. simpl. auto. }
        assert (Heca_ss: env_contracts ss adm = None).
        { subst ss. simpl. auto. }        
        lets H__: IHn Hec_ss Hfd_ss Hech_ss Heca_ss Hcs_ss; eauto.
        specializes H__; eauto.
        clear -Hfmp_h__. tauto.
        clear -Hfmp_a__. tauto.
        {
          introv Hin.
          assert (Hinor: In act (chain_state_queue t) \/ In act l).
          {
            subst ss. simpl in Hin.
            apply in_app_or; auto.
          }
          destruct Hinor as [Hinq | Hinl].
          -
            lets Hso: exe_act_gen_same_orig Ee; eauto.
            specializes Hso; eauto.
            specializes Hacts_; eauto.
            destruct Hacts_ as (Hnac & Hnfo).
            splits.
            + congruence.
            + auto.
            + introv Hfind Heq. false.
            + introv Hfind Heq. false.
          -
            assert (In act (a :: l)).
            { simpl. right; auto. }
            specializes Hacts; eauto.
            destruct Hacts as (Horig' & Hfrm' & Hfmp_h' & Hfmp_a').
            split; auto.
            split; auto. 
            simpl in Htl.
            specializes Htl; eauto.
            split.
            + introv Hfind Hf. false.
            + introv Hfind Hf. false. 
        }
        {
          introv Hintl.
          subst ss.
          simpl in Hintl.
          simpl in Htl.
          revert Htl; introv Htl.
          destruct (chain_state_queue t) eqn: Eque.
          - simpl in Hintl.
            eapply Htl; eauto.
            eapply in_list_tl_in_list; eauto.
          -
            simpl in Hintl.
            apply in_app_or in Hintl; auto.
            destruct Hintl as [Hin1 | Hin2].
            + specializes Hacts_ act; eauto.
              specializes Hacts_; eauto. simpl. right; auto.
              destruct Hacts_; auto.
            + eapply Htl; eauto.
        }

        {
          destruct H__ as (Hfd' & Hec' & Hex').
          destruct Hex' as (cs' & Hcst' & Hfmph' & Hfmpa' & Hn').
          split; auto.
          subst ss. simpl in Hec'. simpl in Hec_ss.
          split. congruence.
          eexists; splits; eauto.
        }        
  Qed.

  Lemma exe_husr_trans_post:
    forall (s s':ChainState) cstate (a: Action) n, 
      transition_reachable miner contract caddr s0 s -> 
      env_contracts s caddr = Some (contract:WeakContract) -> 
      funds s caddr > 0 -> 
      contract_state s caddr = Some cstate ->      
      cstate.(status) = FMap.empty -> 
      transition miner n s a = Ok s' -> 
      (a.(act_origin) = h_usr \/ a.(act_origin) = adm) ->      
      funds s' caddr > 0 /\ 
        env_contracts s' caddr = env_contracts s caddr /\
        exists cs',
          contract_state s' caddr = Some cs' /\
            (FMap.find h_usr cs'.(status) = Some status_requested \/
               FMap.find h_usr cs'.(status) = None) /\ 
            (FMap.find adm cs'.(status) = Some status_requested \/
               FMap.find adm cs'.(status) = None) /\  
            (forall a,
                address_neqb a h_usr = true ->
                address_neqb a adm = true -> 
                FMap.find a cs'.(status) = None). 
  Proof.
    introv Htrc Hec Hfd Hcs Hnone Htrans Hori.
    pose proof caddr_not_husr as Hcnh.
    pose proof caddr_not_adm as Hcna.
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
    assert (Hna: env_contracts s adm = None).
    {
      eapply address_not_contract_not_wc; eauto.
      eapply address_not_contract_negb; eauto.
    }
    lets H__: exe_acts_post ss.
    specializes H__; eauto.
    {
      subst ss. simpl. auto.
    }
    {
      subst ss. unfold funds in *. simpl.
      destruct_address_eq; try congruence.
    }
    {
      subst ss. simpl. auto.
    }
    {
      subst ss. simpl. auto.
    }
    {
      subst ss. simpl.
      unfold add_new_block_to_env.
      simpl.
      unfold contract_state.
      simpl.
      unfolds in Hcs.
      destruct (env_contract_states s caddr); tryfalse.
      simpl in Hcs. rewrite Hcs.
      eauto.
    }
    { rewrite Hnone. left. eauto. }
    { rewrite Hnone. left. eauto. }
    { rewrite Hnone. intros. eauto. }
    {
      subst ss. simpl.
      introv Ha.
      inverts Ha; subst; tryfalse.
      splits.
      - auto.
      - 
        eapply find_invalid_root_ctr_addr with (act:=act) in Efira.
        assert (Hcat: address_is_contract caddr = true).
        {
          eapply contract_addr_format; eauto.
        }
        introv Hf; subst; congruence.
        simpl. auto.
      -
        introv Hf. rewrite Hnone in Hf. false. apply Hf; eauto.
      -
        introv Hf. rewrite Hnone in Hf. false. apply Hf; eauto.
    }
    {
      subst ss.
      simpl.
      introv Hf. false.
    }

    destruct H__ as (Hfd' & Hctr' & Hex').
    destruct Hex' as (cs' & Hcst' & Hfmph' & Hfmpa' & Hfmpn').
    split; auto.
    subst ss.
    simpl in Hctr'.
    split; auto.
    eexists; splits; eauto.
    tauto.
    tauto.
  Qed. 

  Lemma att_step:
    forall sref s, 
      inv2_func sref s ->
      exists s',
        transition miner 1 s attacker_call_reinit = Ok s' /\ 
          funds s' caddr > 0 /\
          (exists st, contract_state s' caddr = Some st /\ status st = FMap.empty). 
  Proof.
    introv Hinv2.
    unfolds in Hinv2.
    destruct Hinv2 as (Htrc & Hfd & Hex).
    destruct Hex as (cs & Hcs & Hfmph & Hfmpa & Hfmpn).
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc as Hqueue_s;eauto.
    rewrite Hqueue_s.
    unfold evaluate_action.
    pose proof get_valid_header_is_valid_header_ as Hvh.
    unfold liqRefut in Hvh; simpl in Hvh.
    rewrite Hvh.
    unfold attacker_call_reinit.  
    simpl.
    assert (Hec_s: env_contracts s caddr = Some (contract:WeakContract)).
    {
      pose proof trans_rc_env_contracts_ as Htc.
      unfold liqRefut in Htc; simpl in Htc.
      eapply Htc; eauto.
    }
    assert (Heq: address_neqb d_usr d_usr = false).
    { eapply address_neqb_eq. auto. }
    rewrite Heq.
    assert (Haicf: address_is_contract d_usr = false).
    { eapply address_not_contract_negb; eauto. }
    rewrite Haicf.
    unfold send_or_call.
    simpl.
    assert (Hrc: reachable s).
    {
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    assert (Hb: env_account_balances s d_usr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    destruct_address_eq;try congruence.
    { pose proof caddr_not_dusr as Hf. congruence. }
    { 
      assert (Hff: (0 >? miner_reward + env_account_balances s d_usr)%address = false).
      { unfold miner_reward. lia. } 
      rewrite Hff.
      simpl.
      rewrite Hec_s.
      unfolds in Hcs.
      destruct (env_contract_states s caddr) eqn: Eecs; tryfalse. 
      simpl.
      simpl in Hcs.
      rewrite Hcs. simpl.
      rewrite deserialize_serialize.
      simpl.
      unfold receivef. simpl.
      rewrite address_eq_refl.
      unfold reinit.
      simpl.
      eexists. split. eauto.
      unfold set_contract_state. 
      unfold funds in *.
      simpl.
      destruct_address_eq; try congruence.
      split. lia.
      unfold contract_state. simpl.
      rewrite address_eq_refl.
      rewrite deserialize_serialize.
      eexists.
      split; eauto.
    }
    {
      pose proof caddr_not_dusr.
      tryfalse.
    }
    {
      assert (Hff: (0 >? env_account_balances s d_usr)%address = false).
      { lia. }
      rewrite Hff.
      simpl.
      rewrite Hec_s. simpl.
      unfolds in Hcs.
      destruct (env_contract_states s caddr) eqn: Eecs; tryfalse. 
      simpl.
      simpl in Hcs.
      rewrite Hcs. simpl.
      rewrite deserialize_serialize.
      simpl.
      unfold receivef. simpl.
      rewrite address_eq_refl.
      unfold reinit.
      simpl.
      eexists. split. eauto.
      unfold set_contract_state. 
      unfold funds in *.
      simpl.
      destruct_address_eq; try congruence.
      split. unfold miner_reward. lia.
      unfold contract_state. simpl.
      rewrite address_eq_refl.
      rewrite deserialize_serialize.
      eexists.
      split; eauto.
    }
    {
      assert (Hff: (0 >? env_account_balances s d_usr)%address = false). 
      { lia. }
      rewrite Hff.
      simpl.
      rewrite Hec_s.
      unfolds in Hcs.
      destruct (env_contract_states s caddr) eqn: Eecs; tryfalse. 
      simpl.
      simpl in Hcs.
      rewrite Hcs. simpl.
      rewrite deserialize_serialize.
      simpl.
      unfold receivef. simpl.
      rewrite address_eq_refl.
      unfold reinit.
      simpl.
      eexists. split. eauto.
      unfold set_contract_state. 
      unfold funds in *.
      simpl.
      destruct_address_eq; try congruence.
      split. lia.
      unfold contract_state. simpl.
      rewrite address_eq_refl.
      rewrite deserialize_serialize.
      eexists.
      split; eauto.
    }
  Qed. 

  Definition well_strat (addrs: list Address) (stt: strat miner addrs) :=
    forall a s0 s (tr: TransitionTrace miner s0 s),  
      List.In a (stt s0 s tr) -> List.In a.(act_origin) addrs. 

  Theorem fm_unsat_strat_liquidity:    
    env_account_balances s0 h_usr >= 1 ->
    forall (hstrat: strat miner [h_usr; adm]), 
      usr_may_deposit hstrat ->
      well_strat [h_usr; adm] hstrat -> 
      ~strat_liquidity miner [h_usr; adm] hstrat [d_usr] attacker_strat contract caddr s0.
  Proof.
    intros Hbal * Humd Hws.
    rewrite <- strat_liq_inst.
    assert (Htrc0: transition_reachable miner contract caddr s0 s0).
    {
      eapply transition_reachable_init_state; eauto.
    }
    lets H__: rft_soundness; eauto.
    eapply H__; eauto; clear H__.
    {
      unfolds.
      pose proof  ie_empmap_funds hstrat Hbal Humd as Hief. 
      destruct Hief as (tr & s & tr' & cs & Hie & Hcs & Hemp & Hfge).
      unfold liqRefut; simpl.
      do 3 eexists; splits; eauto.
      unfold inv1_func.
      splits.
      - eapply transition_reachable_interleavedExecution_transition_reachable;eauto.
      - eauto.
      - eexists; splits; eauto.
    }
    {
      unfolds.
      introv Hor.
      destruct Hor as [Hi1 | Hi2].
      - introv Hf.
        unfolds in Hi1. unfold liqRefut in Hi1; simpl in Hi1.
        unfolds in Hi1.
        destructs Hi1.
        lia.
      - introv Hf.
        unfolds in Hi2. unfold liqRefut in Hi2; simpl in Hi2.
        unfolds in Hi2.
        destructs Hi2.
        lia.
    }    
    {
      unfolds.
      introv Hinv1 Hsd.
      unfolds in Hinv1. unfold liqRefut in Hinv1; simpl in Hinv1.
      unfolds in Hinv1.
      destruct Hinv1 as (Htrc & Hfd & Hex).
      destruct Hex as (st & Hcst & Hemp).
      unfold stratDrive in Hsd.
      destruct Hsd as (a & n & Htrans & Hin & Htr').
      unfold liqRefut in Htrans; simpl in Htrans.
      lets H__: exe_husr_trans_post Htrc.
      pose proof trans_rc_env_contracts_ cs as Hte.
      unfold liqRefut in Hte; simpl in Hte.
      specialize (Hte Htrc).
      specialize (H__ Hte).
      specialize (H__ Hfd Hcst Hemp Htrans).
      unfolds in Hws.
      unfold liqRefut in Hin; simpl in Hin.
      specializes Hws; eauto.
      simpl in Hws.
      specializes H__.
      {
        destruct Hws as [Hl | [Hr | Hf]]; tryfalse; eauto.
      }
      destruct H__ as (Hfd' & Hec' & Hex').
      destruct Hex' as (cs'0 & Hcst' & Hfmph' & Hfmpa' & Hfmpn').
      unfolds. unfold liqRefut; simpl.
      unfolds.
      split.
      eapply transition_reachable_transition_transition_reachable; eauto.
      split; eauto.      
    }
    {
      unfolds.
      introv Hinv2.
      assert (Hinv2_ := Hinv2).
      unfolds in Hinv2_. unfold liqRefut in Hinv2_; simpl in Hinv2_.
      unfolds in Hinv2_.
      destruct Hinv2_ as (Htrc & Hfd & st & Hcs & Hor & Hor_ & Hn). 
      assert (Hnr:
               FMap.find h_usr (status st) = None /\ FMap.find adm (status st) = None \/
                 (FMap.find h_usr (status st) = Some status_requested \/
                    FMap.find adm (status st) = Some status_requested)) by tauto.
      destruct Hnr as [Hnn | Hrr].
      {
        eexists cs. exists tr. eexists.
        split. constructors.
        unfolds. unfold liqRefut; simpl.
        unfold inv1_func.
        splits; eauto.
        eexists; splits; eauto. destruct Hnn.
        eapply fin_maps.map_empty; eauto.
        intros.
        destruct (address_neqb i h_usr) eqn: E1;
          destruct (address_neqb i adm) eqn: E2; tryfalse.
        specializes Hn ;eauto.
        apply address_neqb_eq in E2. subst. auto.
        apply address_neqb_eq in E1. subst. auto.
        apply address_neqb_eq in E1. subst. auto.
      }
      {
        lets H__: att_step Hinv2.
        destruct H__ as (s' & Htrans & Hfd_ & Hex_).
        destruct Hex_ as (st_ & Hcst & Hemp).
        unfolds in Hinv2.
        unfold liqRefut in Hinv2; simpl in Hinv2.
        unfolds in Hinv2.
        destruct Hinv2 as (Htrc_ & Hfd__ & Hex__).
        exists s'. eexists. eexists.
        split.
        2: {
          unfolds. unfold liqRefut; simpl.
          unfolds.
          splits.
          - eapply transition_reachable_transition_transition_reachable; eauto.
          - auto.
          - eexists; splits; eauto.
        }
        eapply MS_Step; eauto.
        eapply MS_Refl; eauto.
        unfold liqRefut; simpl.
        unfolds.
        exists attacker_call_reinit.
        eexists.
        exists Htrans.
        split; eauto.
        unfold attacker_strat.
        unfold liqRefut; simpl.
        rewrite Hcs. 
        destruct Hor as [Hr1 | Hn1]; destruct Hor_ as [Hr2 | Hn2]; destruct Hrr; tryfalse. 
        - rewrite Hr1. simpl. auto. 
        - rewrite Hr1. simpl. auto.
        - rewrite Hr1. simpl. auto.
        - rewrite Hn1. rewrite Hr2. simpl. auto.
      }
    }      
  Qed.     

End Liquidity.  
