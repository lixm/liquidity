
Require Import funds_management_ok.

Section Liquidity.
  
  Let h_usr := funds_management_ok.h_usr.
  Let d_usr := funds_management_ok.d_usr.
  Let adm := funds_management_ok.adm.

  Require Coq.NArith.NArith. 
  Require stdpp.countable.
  Local Open Scope Z_scope.

  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Let caddr := funds_management_ok.caddr.
  Let miner := funds_management_ok.miner.

  Variable s0 : ChainState.
  Hypothesis H_init: is_init_state contract caddr s0.
  Hypothesis H_miner : address_not_contract miner = true.

  Tactic Notation "contract_simpl" := contract_simpl @receive @init.
  Ltac destruct_message :=
    repeat match goal with
      | H : Blockchain.receive _ _ _ _ _ = Ok _ |- _ => unfold Blockchain.receive in H; cbn in H
      | msg : option Msg |- _ => destruct msg
      | msg : Msg |- _ => destruct msg
      | H : Blockchain.receive _ _ _ _ None = Ok _ |- _ => now contract_simpl
      | H : receive _ _ _ None = Ok _ |- _ => now contract_simpl
      end.

  Ltac simpl_eval :=
    match goal with
    (* | H: context[FMap.find ?a ?m] |- _ => destruct (FMap.find a m) eqn: E_; simpl_eval *)
    | H: (if ?e then _ else _) = _ |- _ => destruct e; tryfalse; inverts H; simpl_eval
    | H: Ok _ = Ok _ |- _ => idtac
    | H: _ = Ok _ |- _ => unfolds in H; simpl_eval
    | _ => idtac
    end. 

  Tactic Notation "destruct_cond" hyp(H) ident(E) tactic(tac) :=
    match type of H with
    | context[if ?expr then _ else _] =>
        destruct expr eqn:E; tac
    end.
  
  Tactic Notation "destruct_head" hyp(H) ident(E) tactic(tac) :=
    match type of H with
    | context [match ?expr with _ => _ end] =>
        destruct expr eqn:E; tac
    end.

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

  Lemma reachable_ex_cstate :
    forall bstate,
      reachable bstate ->
      env_contracts bstate caddr = Some (contract : WeakContract) -> 
      exists cstate,
        contract_state bstate caddr = Some cstate /\ 
          (FMap.find h_usr cstate.(status) = None \/
             FMap.find h_usr cstate.(status) = Some status_requested \/
             FMap.find h_usr cstate.(status) = Some status_approved) /\
          cstate.(admin) = adm. 
  Proof.
    intros.
    contract_induction; intros; auto; cbn in *;try congruence;try lia;eauto.
    - unfolds in init_some.
      inverts init_some.
      split.
      + left. simpl. auto.
      + simpl; auto. 
    - unfolds in receive_some.
      destruct_message.
      + simpl_eval; eauto.
        destruct_and_split; simpl; auto.
        lets H_: address_eqb_spec (ctx_origin ctx) h_usr.
        inverts H_.
        rewrite H1. auto.
        rewrite FMap.find_add_ne; eauto.
      + simpl_eval; eauto.
        destruct (FMap.find a (status prev_state)) eqn: E; tryfalse. 
        simpl_eval; eauto.
        {
          simpl.
          lets H_: address_eqb_spec a h_usr.
          inverts H_.
          rewrite FMap.find_add; eauto.
          destruct IH. split; auto.
          rewrite FMap.find_add_ne; eauto.
        }
        {
          simpl.
          lets H_: address_eqb_spec a h_usr.
          inverts H_.
          rewrite FMap.find_remove.
          destruct IH.
          split; auto.
          rewrite FMap.find_remove_ne; eauto.
        }
      + simpl_eval; eauto.
        destruct (FMap.find (ctx_origin ctx) (status prev_state)) eqn: E; tryfalse.
        simpl_eval; eauto.
        simpl.
        lets H_: address_eqb_spec (ctx_origin ctx) h_usr.
        inverts H_.
        {
          rewrite H.
          rewrite FMap.find_remove.
          destruct IH.
          split; eauto.
        }
        {
          rewrite FMap.find_remove_ne; eauto.
        }
      +
        destruct_cond receive_some Ecof tryfalse.
        inverts receive_some. eauto.
    - unfolds in receive_some.
      destruct_message.
      + simpl_eval; eauto.
        destruct_and_split; simpl; auto.
        lets H_: address_eqb_spec (ctx_origin ctx) h_usr.
        inverts H_.
        rewrite H1. auto.
        rewrite FMap.find_add_ne; eauto.
      + simpl_eval; eauto.
        destruct (FMap.find a (status prev_state)) eqn: E; tryfalse. 
        simpl_eval; eauto.
        {
          simpl.
          lets H_: address_eqb_spec a h_usr.
          inverts H_.
          rewrite FMap.find_add; eauto.
          destruct IH. split; auto.
          rewrite FMap.find_add_ne; eauto.
        }
        {
          simpl.
          lets H_: address_eqb_spec a h_usr.
          inverts H_.
          rewrite FMap.find_remove.
          destruct IH.
          split; auto.
          rewrite FMap.find_remove_ne; eauto.
        }
      + simpl_eval; eauto.
        destruct (FMap.find (ctx_origin ctx) (status prev_state)) eqn: E; tryfalse.
        simpl_eval; eauto.
        simpl.
        lets H_: address_eqb_spec (ctx_origin ctx) h_usr.
        inverts H_.
        {
          rewrite H.
          rewrite FMap.find_remove.
          destruct IH.
          split; eauto.
        }
        {
          rewrite FMap.find_remove_ne; eauto.
        }
      +
        destruct_cond receive_some Ecof tryfalse. 
        inverts receive_some. eauto.
    -
      solve_facts.
  Qed.

  Definition var_func (csref cs: ChainState) : option nat :=
    match contract_state cs caddr with
    | Some st => 
        match FMap.find h_usr st.(status) with
        | None => (if 0 <? (env_account_balances cs caddr) then Some 3%nat else Some 0%nat)
        | Some n =>
            if Nat.eqb n status_requested then 
              Some (2%nat)
            else
              if Nat.eqb n status_approved then
                Some (1%nat)
              else 
                None
        end
    | None => None
    end.

  Definition inv_func (cs_ref cs: ChainState) : Prop :=
    transition_reachable miner contract caddr s0 cs /\ 
      exists st,
        contract_state cs caddr = Some st /\ 
          (FMap.find h_usr st.(status) = None \/
             FMap.find h_usr st.(status) = Some status_requested \/
             FMap.find h_usr st.(status) = Some status_approved) /\
          st.(admin) = adm. 
  
  Program Instance liqVerif : LiqVerif := {
      A := nat;
      Ord := Nat.lt;
      Inv := inv_func;
      Var := var_func;

      setup := Setup;
      msg := Msg; 
      state := State;
      error := Error;

      cur_adr := caddr;
      inist := s0;
      theCtr := contract; 

      miner_adr := miner;
      H_mnctr := H_miner; 
    }. 
  Next Obligation.
    eapply well_founded_lt_compat.
    introv Hnlt.
    instantiate (1:=fun n => n).
    simpl.
    lia.
  Defined.
  Next Obligation.
    introv Hlt1 Hlt2.
    lia.
  Defined.
  
  Definition well_strat (addrs: list Address) (stt: strat miner addrs) :=
    forall a s0 s (tr: TransitionTrace miner s0 s),  
      List.In a (stt s0 s tr) -> List.In a.(act_origin) addrs. 

  Hypothesis h_usr_eoa : address_not_contract h_usr = true.
  Hypothesis d_usr_eoa : address_not_contract d_usr = true.
  Hypothesis adm_eoa : address_not_contract adm = true.

  (* Definition usr_deposit: Action := *)
  (*   build_transfer h_usr caddr 1. *)

  Definition usr_call_reqWithdrawal: Action :=
    build_call h_usr caddr 0 ReqWithdrawal.

  Definition usr_call_withdraw: Action :=
    build_call h_usr caddr 0 Withdraw.

  Definition adm_call_processReq (a: Address): Action :=
    build_call adm caddr 0 (ProcessReq a true).

  Definition honest_strat : (strat miner [h_usr; adm]) :=
    fun s0 (s: ChainState) tr =>
      match @contract_state _ State Hser_state s caddr with
      | Some state =>
          match FMap.find h_usr state.(status) with
            None => [usr_call_reqWithdrawal]
          | Some b =>
              if (b =? status_requested)%nat then 
                [adm_call_processReq h_usr]
              else
                if (b =? status_approved)%nat then
                  [usr_call_withdraw]
                else
                  []
          end
      | None => []
      end.

  Lemma min_zero:
    forall a, minimal a -> a = 0%nat.
  Proof.
    introv Hm.
    unfolds in Hm.
    unfold Ord in Hm; unfold liqVerif in Hm.
    destruct a.
    auto.
    false.
    specialize (Hm 0%nat).
    apply Hm.
    lia.
  Qed.  

  Lemma inv_var_def:
    forall csref cs, 
      Inv csref cs -> Var csref cs <> None.
  Proof.
    introv Hinv.
    unfolds in Hinv; unfold liqVerif in Hinv.
    unfolds in Hinv.
    destruct Hinv as (_ & Hex).
    destruct_and_split.
    unfold Var; unfold liqVerif.
    unfold var_func.

    rewrite H.
    destruct H0 as [Hn | [Hreq | Hapr]].
    - 
      rewrite Hn.
      destruct (0 <? env_account_balances cs caddr); eauto.
    -
      rewrite Hreq.
      rewrite Nat.eqb_refl.
      eauto.
    -
      rewrite Hapr.
      unfold status_approved, status_requested.
      simpl.
      eauto.
  Qed.

  Lemma min_bal_zero: 
    forall csref cs,
      Inv csref cs -> 
      var_func csref cs = Some 0%nat -> 
      funds cs caddr = 0. 
  Proof.
    introv Hinv Hvf.
    unfolds in Hvf.
    unfold Inv in Hinv; unfold liqVerif in Hinv.
    unfolds in Hinv.
    destruct Hinv as (Htrc & Hex).
    destruct_and_split.
    rewrite H in Hvf.
    destruct (FMap.find h_usr (status x)); tryfalse.
    destruct ((n =? status_requested)%nat); tryfalse. 
    destruct ((n =? status_approved)%nat); tryfalse.
    destruct (0 <? env_account_balances cs caddr) eqn: E; tryfalse.
    lets H_: Z.ltb_spec0 0 (env_account_balances cs caddr).
    inverts H_; tryfalse.
    assert (Hfge: funds cs caddr >= 0).
    {
      eapply reachable_funds_nonnegative; eauto.
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    unfold funds in *.
    lia.
  Qed.

  Lemma exe_act_preserves_status:
    forall (s s':ChainState) cstate (a: Action) 
           (Hec_s: env_contracts s caddr = Some (contract:WeakContract)),
      contract_state s caddr = Some cstate ->
      execute_action a s.(chain_state_env) = Ok s' ->
      a.(act_origin) <> cstate.(admin) ->
      a.(act_origin) <> h_usr ->
      a.(act_from) <> h_usr ->
      env_contracts s' caddr = env_contracts s caddr /\
        env_contracts s' h_usr = env_contracts s h_usr /\ 
        exists cs',
          contract_state s' caddr = Some cs' /\
            FMap.find h_usr cs'.(status) = FMap.find h_usr cstate.(status) /\
            cs'.(admin) = cstate.(admin).
  Proof.
    do 5 intro.
    introv Hcs (* Htrc *) Hexe Hnoa Hno Hne.
    unfolds in Hexe.
    destruct a eqn: Ea.
    destruct act_body eqn: Eb.
    simpl in Hne.
    - unfolds in Hexe.
      destruct (amount <? 0) eqn: Eamt; tryfalse.
      destruct (amount >? env_account_balances s act_from) eqn: Eamt'; tryfalse.
      destruct (env_contracts s to) eqn: Eec; tryfalse.
      +
        destruct (env_contract_states s to) eqn: Ees; tryfalse.
        simpl in Hexe.
        destruct_address_eq;try congruence.
        destruct_head Hexe Ewc tryfalse.
        simpl in Hexe.
        subst act_from.
        destruct t.
        inverts Hexe.
        simpl.
        unfold contract_state.
        simpl. 
        destruct_address_eq;try congruence.
        *
          unfolds in Ewc.
          destruct w.
          subst to.
          rewrite Hec_s in Eec.
          inverts Eec. simpl in Ewc.
          destruct (result_of_option (deserialize s1) deser_error) eqn: Ero; tryfalse.
          destruct_head Ewc Eee tryfalse.
          destruct t0. simpl in Ewc. inverts Ewc.
          rewrite deserialize_serialize.
          split; auto.
          split; auto.
          eexists.
          unfolds in Hcs.
          simpl in Hcs.
          destruct (env_contract_states s caddr) eqn: Eec; tryfalse.
          inverts Ees.
          rewrite Hcs in Ero.
          simpl in Ero.
          inverts Ero.
          split; auto.
          unfold receive in Eee. simpl in Eee.
          destruct_cond Eee Ecc tryfalse.
          simpl in Eee. inverts Eee. split; auto.
        *
          unfolds in Hcs.
          simpl in Hcs.
          destruct (env_contract_states s caddr) eqn: Eecs; tryfalse.
          split; auto.
          split; auto.
          eexists.
          split; eauto.
        *
          destruct_head Hexe Ewc tryfalse.
          destruct t.
          inverts Hexe.
          simpl.
          unfold contract_state.
          simpl.
          destruct_address_eq;try congruence.
          **
            unfold wc_receive in Ewc.
            destruct w.
            subst to. 
            rewrite Hec_s in Eec.
            inverts Eec.
            destruct (result_of_option (deserialize s1) deser_error) eqn: Ero; tryfalse.
            destruct_head Ewc Eee tryfalse.
            destruct t0.
            simpl in Ewc. inverts Ewc.
            rewrite deserialize_serialize.
            split; auto.
            split; auto.
            eexists.
            split; eauto.
            unfold receive in Eee. simpl in Eee.
            destruct_cond Eee Ecc tryfalse.
            simpl in Eee. inverts Eee.
            unfolds in Hcs.
            simpl in Hcs.
            destruct (env_contract_states s caddr) eqn: Eec; tryfalse.
            inverts Ees.
            rewrite Hcs in Ero.
            simpl in Ero.
            inverts Ero.
            split; auto.
          **
            unfolds in Hcs.
            simpl in Hcs.
            destruct (env_contract_states s caddr) eqn: Eecs; tryfalse.
            rewrite Hcs.
            split; auto.
            split; auto.
            eexists.
            split; eauto.
      +
        destruct (address_is_contract to) eqn: Eic; tryfalse.
        inverts Hexe.
        simpl.
        unfold contract_state.
        simpl.
        unfolds in Hcs.
        simpl in Hcs.
        destruct (env_contract_states s caddr) eqn: Ee; tryfalse.
        rewrite Hcs.
        split; auto.
        split; auto.
        eexists.
        splits; eauto.
    -
      simpl in Hne.
      simpl in Hno.
      simpl in Hnoa.
      unfolds in Hexe.
      destruct (amount <? 0) eqn: Eamt; tryfalse.
      destruct (amount >? env_account_balances s act_from) eqn: Eamt'; tryfalse.
      destruct (env_contracts s to) eqn: Eec; tryfalse.
      +
        destruct (env_contract_states s to) eqn: Eecs; tryfalse.
        destruct_head Hexe Erc tryfalse. 
        simpl in Hexe.
        destruct t.
        inverts Hexe.
        simpl in Erc.
        unfold wc_receive in Erc.
        destruct w.
        unfold contract_state.
        simpl.
        destruct (caddr =? to)%address eqn: Ecte.
        *
          assert (caddr = to).
          { lets H_: address_eqb_spec caddr to. inverts H_; tryfalse; auto. }
          subst to.
          rewrite Hec_s in Eec.
          inverts Eec.
          simpl in Erc.
          destruct (result_of_option (deserialize s1) deser_error) eqn: Eds1; tryfalse.
          destruct (result_of_option (deserialize msg) deser_error) eqn: Em; tryfalse.
          destruct_head Erc Eee tryfalse; destruct t0; tryfalse.
          ** 
            unfold receive in Eee.
            simpl in Eee.
            unfold reqWithdrawal in Eee.
            simpl in Eee.
            destruct_cond Eee Ecc tryfalse.
            destruct_cond Eee Ec_ tryfalse.
            destruct_head Eee Ecc_ tryfalse.
            simpl in Eee. inverts Eee.
            simpl in Erc. inverts Erc.
            rewrite deserialize_serialize.
            split; auto.
            split; auto.
            eexists.
            split; eauto.
            simpl.
            unfolds in Hcs.
            simpl in Hcs.
            destruct (env_contract_states s caddr) eqn: E_; tryfalse.
            inverts Eecs.
            rewrite Hcs in Eds1.
            simpl in Eds1. inverts Eds1.
            split; eauto.
          **
            unfold receive in Eee.
            simpl in Eee.
            destruct_cond Eee Ecc tryfalse.
            unfold processReq in Eee.
            simpl in Eee.
            destruct_head Eee Ecc_ tryfalse. 
            destruct_cond Eee Ec_ tryfalse.
            destruct_cond Eee Eb_ tryfalse.
            ***
              simpl in Eee. inverts Eee.
              simpl in Erc. inverts Erc.
              rewrite deserialize_serialize.
              split; auto.
              split; auto.
              eexists.
              split; eauto.
              simpl.
              unfolds in Hcs.
              simpl in Hcs.
              destruct (env_contract_states s caddr) eqn: E_; tryfalse. 
              inverts Eecs.
              rewrite Hcs in Eds1.
              simpl in Eds1.
              inverts Eds1.
              lets H_: address_eqb_spec act_origin (admin t).
              inverts H_.
              false.
              rewrite <- H in Ec_. simpl in Ec_. false.
            ***
              simpl in Eee. inverts Eee.
              simpl in Erc. inverts Erc.
              rewrite deserialize_serialize.
              split; auto.
              split; auto.
              eexists.
              split; eauto.
              simpl.
              unfolds in Hcs.
              simpl in Hcs.
              destruct (env_contract_states s caddr) eqn: E_; tryfalse. 
              inverts Eecs.
              rewrite Hcs in Eds1.
              simpl in Eds1.
              inverts Eds1.
              lets H_: address_eqb_spec act_origin (admin t).
              inverts H_.
              false.
              rewrite <- H in Ec_. simpl in Ec_. false.
          **
            unfold receive in Eee.
            simpl in Eee.
            destruct_cond Eee Ec_ tryfalse.
            unfold withdraw in Eee.
            simpl in Eee.
            destruct_head Eee Ecc_ tryfalse. 
            destruct_cond Eee Ecc__ tryfalse.
            simpl in Eee.
            inverts Eee.
            simpl in Erc.
            inverts Erc.
            split; auto.
            split; auto.
            rewrite deserialize_serialize.
            eexists.
            split; eauto.
            unfolds in Hcs.
            destruct (env_contract_states s caddr) eqn: E_; tryfalse.
            simpl in Hcs.
            inverts Eecs.
            rewrite Hcs in Eds1.
            simpl in Eds1.
            inverts Eds1.
            simpl.
            split; auto.
            apply not_eq_sym in Hno. 
            rewrite FMap.find_remove_ne; eauto.
        *
          unfolds in Hcs.
          simpl in Hcs.
          destruct (env_contract_states s caddr) eqn: Ee; tryfalse. 
          rewrite Hcs.
          split; auto.
          split; auto.
          eexists.
          splits; eauto.
      +
        destruct (address_is_contract to); tryfalse.
    -
      simpl in Hnoa, Hno, Hne.
      unfolds in Hexe.
      destruct (amount <? 0) eqn: Eamt; tryfalse.
      destruct (amount >? env_account_balances s act_from) eqn: Eamt'; tryfalse.
      destruct (get_new_contract_addr s) eqn: En; tryfalse. 
      destruct (correct_contract_addr s a0) eqn: Ecca; tryfalse.
      destruct_head Hexe Ewi tryfalse. 
      inverts Hexe.
      simpl.
      unfold contract_state.
      simpl.
      lets H__: address_eqb_spec caddr a0.
      inverts H__.
      + 
        unfolds in Ecca.
        destruct (isNone (env_contracts s a0)) eqn: Enn.
        unfolds in Enn.
        destruct (env_contracts s a0) eqn: Eea; tryfalse.
        rewrite andb_false_r in Ecca.
        false. 
      +
        unfolds in Hcs.
        simpl in Hcs.
        destruct (env_contract_states s caddr) eqn: E; tryfalse. 
        rewrite Hcs.
        split; auto.
        unfolds in Ecca.
        destruct (address_is_contract a0) eqn: Ea0.
        2: { simpl in Ecca. false. }
        assert (Hneq: a0 <> h_usr).
        {
          eapply addr_ctr_neq; eauto.
        }
        apply address_eq_ne in Hneq.
        rewrite address_eq_sym in Hneq.
        rewrite Hneq.
        split; auto.
        eexists.
        split; eauto.
  Qed.

  Lemma addr_not_ctr_none: 
    forall a s,
      reachable s -> 
      address_not_contract a = true -> 
      env_contracts s a = None.
  Proof.
    introv Hrc Hanc.
    destruct (env_contracts s a) eqn: E.
    - specialize (contract_addr_format a w Hrc E).
      introv Hf.
      unfold address_not_contract in Hanc.
      rewrite Hf in Hanc.
      false.
    - auto.
  Qed.

  Lemma exe_acts_preserves_status_d_usr:
    forall n (s s': ChainState) cs, 
      env_contracts s caddr = Some (contract: WeakContract) -> 
      contract_state s caddr = Some cs ->    
      execute_actions n s true = Ok s' -> 
      env_contracts s h_usr = None -> 
      (forall a, List.In a s.(chain_state_queue) ->
                 a.(act_origin) <> cs.(admin) /\ a.(act_origin) <> h_usr /\ a.(act_from) <> h_usr) -> 
      exists cs',
        contract_state s' caddr = Some cs' /\
          FMap.find h_usr cs'.(status) = FMap.find h_usr cs.(status) /\ 
          cs'.(admin) = cs.(admin). 
  Proof.
    induction n.
    -
      introv Hec Hcs Hexea Hech. simpl in Hexea.
      destruct_head Hexea E tryfalse.
      inverts Hexea.
      simpl.
      eexists.
      splits; eauto.
    -
      introv Hec_s Hcs Hexe Hech Hane.
      assert (Hane_ := Hane).
      simpl in Hexe.
      destruct_head Hexe E idtac.
      + 
        inverts Hexe.
        simpl.
        eexists.
        splits; eauto.
      +
        destruct_head Hexe Ee tryfalse. 
        lets H__: exe_act_preserves_status Hec_s Hcs Ee.
        specialize (Hane a).
        specializes Hane. { simpl. eauto. }
        destruct Hane as (Hoa_ne & Hoh_ne & Hfh_ne).
        specializes H__; eauto.
        destruct H__ as (Hecc & Hech_ & Hex).
        destruct Hex as (cs' & Hcs' & Hfeq' & Hadeq').
        remember {| chain_state_env := t; chain_state_queue := chain_state_queue t ++ l |} as ss.
        assert (Hcsca: contract_state ss caddr = Some cs').
        {
          rewrite Heqss. simpl. auto.
        }
        assert (Heceq: env_contracts ss caddr = Some (contract: WeakContract)).
        {
          subst ss. simpl. congruence. 
        }
        lets IH_: IHn Heceq Hcsca Hexe.
        assert (Ha: forall a : Action,
                   In a (chain_state_queue ss) ->
                   act_origin a <> admin cs /\ act_origin a <> h_usr /\ act_from a <> h_usr).
        {
          introv Hin.
          rewrite Heqss in Hin.
          simpl in Hin.
          apply in_app_or in Hin.
          destruct Hin as [Hinqt | Hinl].
          - unfolds in Ee.
            destruct a eqn: Ea.
            destruct act_body eqn: Eb; simpl in *.
            + unfolds in Ee.
              destruct (amount <? 0); tryfalse.
              destruct (amount >? env_account_balances s act_from); tryfalse.
              destruct (env_contracts s to) eqn: Eto; tryfalse.
              *
                destruct (env_contract_states s to); tryfalse.
                destruct_head Ee E_ tryfalse. 
                destruct t0.
                inverts Ee.
                simpl in Hinqt.
                lets H_: in_act_org_frm Hinqt.
                destruct H_ as (Ho_ & Hf_).
                rewrite Ho_.
                rewrite Hf_.
                splits; try congruence; eauto.
              *
                destruct (address_is_contract to); tryfalse.
                inverts Ee.
                simpl in Hinqt.
                false.
            +
              unfolds in Ee.
              destruct (amount <? 0); tryfalse.
              destruct (amount >? env_account_balances s act_from); tryfalse.
              destruct (env_contracts s to) eqn: Eto; tryfalse.
              *
                destruct (env_contract_states s to); tryfalse.
                destruct_head Ee E_ tryfalse. 
                destruct t0.
                inverts Ee.
                simpl in Hinqt.
                lets H_: in_act_org_frm Hinqt.
                destruct H_ as (Ho_ & Hf_).
                rewrite Ho_.
                rewrite Hf_.
                splits; try congruence; eauto.
              *
                destruct (address_is_contract to); tryfalse.
            +
              unfolds in Ee.
              destruct (amount <? 0); tryfalse.
              destruct (amount >? env_account_balances s act_from); tryfalse.
              destruct (get_new_contract_addr s) eqn: Enc; tryfalse.
              destruct (correct_contract_addr s a1) eqn: Ecca; tryfalse.
              destruct_head Ee E_ tryfalse. 
              inverts Ee.
              simpl in Hinqt.
              false. 
          - assert (Hin': List.In a0 (a :: l)).
            {
              simpl. right; auto.
            }
            specialize (Hane_ _ Hin').
            auto.
        }
        assert (Hhnone: env_contracts ss h_usr = None).
        {
          eapply contract_nondeployed_preserved_by_act; eauto.
        }
        rewrite Hadeq' in IH_.
        specialize (IH_ Hhnone Ha). 
        destruct IH_ as (cs__ & Hcs__ & Hfdeq__ & Hadeq__).
        eexists.
        splits; eauto; try congruence.
  Qed.
  
  Hypothesis addr_neq : adm <> h_usr /\ adm <> d_usr /\ h_usr <> d_usr.

  Lemma transition_preserves_status_d_usr:
    forall (s s':ChainState) cstate (a: Action) n, 
      contract_state s caddr = Some cstate ->
      transition_reachable miner  contract caddr s0 s ->
      transition miner n s a = Ok s' ->
      a.(act_origin) = d_usr -> 
      exists cs',
        contract_state s' caddr = Some cs' /\
          FMap.find h_usr cs'.(status) = FMap.find h_usr cstate.(status) /\ 
          cs'.(admin) = cstate.(admin). 
  Proof.
    introv Hcs Htrc Htrans Horig.
    unfolds in Htrans.
    destruct (queue_isb_empty s); tryfalse.
    destruct (evaluate_action n s (get_valid_header miner s) [a]) eqn: Ee; tryfalse.
    unfolds in Ee.
    destruct (validate_header (get_valid_header miner s) s) eqn: Evh; tryfalse. 
    destruct (find_origin_neq_from [a]) eqn: Efo; tryfalse.
    destruct (find_invalid_root_action [a]) eqn: Eivr; tryfalse.
    inverts Htrans.
    assert (Hrc: reachable s).
    {
      specialize (transition_reachable_impl_reachable miner contract caddr s0 s H_init Htrc).
      auto.
    }

    lets H__: exe_acts_preserves_status_d_usr Ee; eauto.
    {
      simpl. auto.
      pose proof trans_rc_env_contracts as HH.
      unfold liqVerif in HH; simpl in HH.
      eapply HH in H_init; eauto.
    }
    eapply H__; eauto.
    {
      simpl. eapply addr_not_ctr_none; eauto.
    }
    introv Hin.
    simpl in Hin.
    inverts Hin; subst; tryfalse.
    rewrite Horig.
    lets Hctr: trans_rc_env_contracts Htrc.
    unfold miner_adr, theCtr, cur_adr, inist, liqVerif in Hctr.
    specialize (Hctr Htrc).
    lets H_: reachable_ex_cstate Hrc Hctr.
    destructs addr_neq.
    protect addr_neq.
    destruct_and_split.
    introv Hf; false.
    introv Hf; false.
    unfolds in Efo.
    simpl in Efo.
    destruct (address_neqb (act_origin a0) (act_from a0)) eqn: E; tryfalse. 
    unfolds in E.
    lets H_: address_eqb_spec (act_origin a0) (act_from a0).    
    inverts H_; tryfalse; eauto.
    introv Hf; congruence.
    rewrite <- H5 in E.
    simpl in E.
    false. 
  Qed.

  Lemma att_strat_drive_preserves_status:
    forall (s s':ChainState) cstate (att_strat: strat miner [d_usr]) tr tr', 
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      stratDrive miner [d_usr] att_strat s0 s tr s' tr' ->
      well_strat [d_usr] att_strat -> 
      exists cs',
        contract_state s' caddr = Some cs' /\
          FMap.find h_usr cs'.(status) = FMap.find h_usr cstate.(status) /\ 
          cs'.(admin) = cstate.(admin). 
  Proof.
    introv Hcs Htrc Hsd Hws.
    inverts Hsd.
    destruct H as (n & Htrans & Hin & Htr').
    unfolds in Hws.
    lets H__: Hws Hin.
    unfolds in H__.
    destruct H__.
    2: false. 
    specialize (transition_preserves_status_d_usr s s' cstate x n Hcs Htrc Htrans).
    introv H_.
    specializes H_; eauto.
  Qed.

  Lemma att_multi_strat_drive_preserves_status:
    forall n (s s':ChainState) cstate (att_strat: strat miner [d_usr]) tr tr', 
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      multiStratDrive miner [d_usr] att_strat s0 s tr s' tr' n -> 
      well_strat [d_usr] att_strat -> 
      transition_reachable miner contract caddr s0 s' /\ 
        exists cs',
          contract_state s' caddr = Some cs' /\
            FMap.find h_usr cs'.(status) = FMap.find h_usr cstate.(status) /\ 
            cs'.(admin) = cstate.(admin). 
  Proof.
    induction n.
    -
      intros.
      inverts H1.
      split; auto.
      eexists.
      split; eauto.
      false.
      lia.
    -
      introv Hcs Htrc Hmsd Hws.
      inverts Hmsd.
      assert (count = n) by lia.
      subst.
      specialize (IHn s s'0 cstate att_strat tr tr'0 Hcs Htrc H2 Hws).
      destruct IHn as (Htrc_ & cs' & Hcs' & Hfmh & Hadm).
      specialize (transition_reachable_multiStratDrive_transition_reachable
                    miner s0 s s'0 tr att_strat [d_usr] contract caddr tr'0 n).
      introv Htrc__.
      specializes Htrc__; eauto.
      specialize (transition_reachable_stratDrive_transition_reachable
                    miner s0 s'0 tr'0 [d_usr] att_strat s' contract caddr tr').
      introv Htrc'.
      split.
      specializes Htrc'; eauto. 
      specialize (att_strat_drive_preserves_status s'0 s' cs' att_strat tr'0 tr' Hcs' Htrc_ H3 Hws).
      introv Hex.
      destruct Hex as (cs'0 & Hcs'0 & Hfh'0 & Had'0).
      eexists.
      split; eauto.
      split; congruence.
  Qed.        

  Lemma fm_eq_var_preserved_nmin:
    forall (csref cs cs': ChainState) st st' a, 
      contract_state cs caddr = Some st ->
      contract_state cs' caddr = Some st' ->
      FMap.find h_usr (status st') = FMap.find h_usr (status st) ->
      Var csref cs = Some a ->
      exists a',  Var csref cs' = Some a' /\ (~ minimal a -> Ord a' a \/ a' = a). 
  Proof.
    introv Hst Hst' Hfmeq.
    unfold Var; unfold liqVerif.
    unfold var_func.
    rewrite Hst. rewrite Hst'. 
    rewrite Hfmeq.
    introv Ha.
    destruct (FMap.find h_usr (status st)); tryfalse; eauto.
    destruct (0 <? env_account_balances cs caddr) eqn: E; tryfalse.
    -
      inverts Ha.
      destruct (0 <? env_account_balances cs' caddr) eqn: E'; eauto.
      eexists; splits; eauto.
      introv Hnm.
      left. unfold Ord; unfold liqVerif. lia.
    -
      inverts Ha.
      destruct (0 <? env_account_balances cs' caddr).
      eexists; splits; eauto.
      introv Hnmin.
      false.
      apply Hnmin.
      unfold minimal. introv Hord. unfold Ord in Hord; unfold liqVerif in Hord.
      lia.
      eexists; splits; eauto.
  Qed. 

  Lemma usr_req_transition_correct: 
    forall (s:ChainState) (cstate: State),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = None -> 
      transition_reachable miner contract caddr s0 s ->
      address_neqb h_usr cstate.(admin) = true -> 
      exists s',
        transition miner 5 s usr_call_reqWithdrawal = Ok s' /\ 
          funds s' caddr = funds s caddr /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = Some status_requested /\ 
              cs.(admin) = cstate.(admin).
  Proof.
    introv Hcs Hst Htrc_s Haneq.
    eexists. 
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    unfold evaluate_action.
    pose proof get_valid_header_is_valid_header as Hvhd.
    unfold liqVerif in Hvhd; simpl in Hvhd.
    rewrite Hvhd; auto.
    unfold usr_call_reqWithdrawal.
    simpl.
    destruct_address_eq;try congruence.
    simpl in Haneq; false.
    simpl.
    assert (Hec_s: env_contracts s caddr = Some (contract:WeakContract)).
    {
      pose proof trans_rc_env_contracts as Htr.
      unfold liqVerif in Htr; simpl in Htr.
      eapply Htr; eauto.
    }
    assert (Hd_nc: address_is_contract h_usr = false).
    {
      eapply address_not_contract_negb; eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert (Hrc: reachable s).
    {
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    assert (Hb: env_account_balances s h_usr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    rewrite Hd_nc.
    unfold send_or_call.
    simpl.

    rewrite Hec_s; simpl.

    unfolds in Hcs.
    destruct (env_contract_states s caddr) eqn: E; tryfalse.
    simpl in Hcs.
    rewrite Hcs.
    simpl.
    rewrite deserialize_serialize.
    simpl.
    unfold receive; simpl.
    rewrite address_eq_refl; simpl.
    unfold reqWithdrawal.
    simpl.
    asserts_rewrite (address_neqb h_usr (admin cstate) = true).
    { apply adr_neq_reflect in n; auto.  }
    rewrite Hst.
    simpl.
    dc Eee tryfalse.
    {
      false. destruct_address_eq; try congruence.
      unfold miner_reward in Eee.  lia. lia.
    }
    simpl.
    split; eauto.
    split.
    {
      unfolds.
      simpl.
      destruct_address_eq;try congruence.
      lia.
      assert (caddr <> miner).
      { eapply addr_ctr_neq; eauto. }
      false.      
      lia.
    }
    {
      eexists. simpl.
      split.
      unfolds. simpl.
      rewrite address_eq_refl.
      rewrite deserialize_serialize.
      eauto.
      split.
      simpl; auto.
      simpl; auto.
    }
  Qed.     
  
  Lemma usr_req_strat_drive:  
    forall (s:ChainState) (cstate: State) (tr: TransitionTrace miner s0 s),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = None -> 
      transition_reachable miner contract caddr s0 s ->
      address_neqb h_usr cstate.(admin) = true -> 
      exists s' tr', 
        stratDrive miner [h_usr; adm] honest_strat s0 s tr s' tr' /\ 
          funds s' caddr = funds s caddr /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = Some status_requested /\
              cs.(admin) = cstate.(admin).
  Proof.
    introv Hcs Hnone Htrc Hneqa.
    lets H__: usr_req_transition_correct Hcs Hnone Htrc Hneqa.
    protect addr_neq.
    destruct_and_split.
    exists x. 
    eexists.
    split.
    exists usr_call_reqWithdrawal. eexists. exists H.
    split.
    unfold honest_strat.
    unfold liqVerif. simpl.
    rewrite Hcs. rewrite Hnone.
    simpl; auto.
    eauto.
    split; auto.
    eexists. splits; eauto.
  Qed.

  Lemma adm_apr_transition_correct: 
    forall (s:ChainState) (cstate: State),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = Some status_requested -> 
      cstate.(admin) = adm -> 
      transition_reachable miner contract caddr s0 s ->
      exists s',
        transition miner 5 s (adm_call_processReq h_usr) = Ok s' /\  
          funds s' caddr = funds s caddr /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = Some status_approved /\ 
              cs.(admin) = cstate.(admin).
  Proof.
    introv Hcs Hst Hadm Htrc_s.
    eexists. 
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    unfold evaluate_action.
    pose proof get_valid_header_is_valid_header as Hvhd.
    unfold liqVerif in Hvhd; simpl in Hvhd.
    rewrite Hvhd; eauto.
    unfold adm_call_processReq. 
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s: env_contracts s caddr = Some (contract:WeakContract)).
    {
      pose proof trans_rc_env_contracts as Htr.
      unfold liqVerif in Htr; simpl in Htr.
      eapply Htr; eauto.
    }
    assert (Hd_nc: address_is_contract adm = false).
    {
      eapply address_not_contract_negb; eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert (Hrc: reachable s).
    {
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    assert (Hb: env_account_balances s adm >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    rewrite Hd_nc.
    unfold send_or_call.
    simpl.

    rewrite Hec_s.
    unfold contract_state in Hcs.
    simpl in Hcs.
    destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
    simpl.
    rewrite Hcs.
    simpl.
    setoid_rewrite deserialize_serialize.
    simpl.
    unfold receive.
    simpl.
    rewrite address_eq_refl.
    simpl.
    unfold processReq. 
    rewrite Hst.
    simpl.
    asserts_rewrite (((adm =? admin cstate)%address) = true).
    {
      lets H__: address_eqb_spec adm (admin cstate).
      inverts H__; tryfalse; auto.
    }
    simpl.
    dc Eee idtac.
    {
      false. destruct_address_eq; try congruence.
      unfold miner_reward in Eee; lia. lia.
    }
    simpl.
    split; eauto.
    split.
    {
      unfolds.
      simpl.
      destruct_address_eq;try congruence; try lia.
      assert (caddr <> miner).
      { eapply addr_ctr_neq; eauto. }
      false.      
    }
    {
      eexists. simpl. 
      split.
      unfolds. simpl.
      rewrite address_eq_refl.
      rewrite deserialize_serialize.
      eauto.
      split.
      simpl; auto.
      simpl; auto.
    }
  Qed.     
      
  Lemma adm_apr_strat_drive:  
    forall (s:ChainState) (cstate: State) (tr: TransitionTrace miner s0 s),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = Some status_requested ->
      cstate.(admin) = adm -> 
      transition_reachable miner contract caddr s0 s ->
      exists s' tr', 
        stratDrive miner [h_usr; adm] honest_strat s0 s tr s' tr' /\ 
          funds s' caddr = funds s caddr /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = Some status_approved /\  
              cs.(admin) = cstate.(admin).
  Proof.
    introv Hcs Hreq Hadm Htrc.
    lets H__: adm_apr_transition_correct Hcs Hreq Hadm Htrc.
    protect addr_neq.
    destruct_and_split.
    exists x. 
    eexists.
    split.
    exists (adm_call_processReq h_usr). eexists. exists H.
    split.
    unfold honest_strat.
    unfold liqVerif. simpl.
    rewrite Hcs. rewrite Hreq.
    simpl; auto.
    eauto.
    split; auto.
    eexists. splits; eauto.
  Qed.

  Lemma usr_wth_transition_correct: 
    forall (s:ChainState) (cstate: State),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = Some status_approved ->  
      transition_reachable miner contract caddr s0 s ->
      exists s',
        transition miner 5 s (usr_call_withdraw) = Ok s' /\   
          funds s' caddr = 0 /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = None /\ 
              cs.(admin) = cstate.(admin).
  Proof.
    introv Hcs Hst Htrc_s.
    eexists. 
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    unfold evaluate_action.
    pose proof get_valid_header_is_valid_header as Hvhd.
    unfold liqVerif in Hvhd; simpl in Hvhd.
    rewrite Hvhd; auto.
    unfold usr_call_withdraw.  
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s: env_contracts s caddr = Some (contract:WeakContract)).
    {
      pose proof trans_rc_env_contracts as Htr.
      unfold liqVerif in Htr; simpl in Htr.
      eapply Htr; eauto.
    }
    assert (Hd_nc: address_is_contract h_usr = false).
    {
      eapply address_not_contract_negb; eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert (Hrc: reachable s).
    {
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    assert (Hb: env_account_balances s h_usr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    assert (Hc: env_account_balances s caddr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    rewrite Hd_nc.
    unfold send_or_call.
    simpl.

    rewrite Hec_s.
    unfold contract_state in Hcs.
    simpl in Hcs.
    destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
    simpl.
    rewrite Hcs.
    simpl.
    setoid_rewrite deserialize_serialize.
    simpl.
    unfold receive; simpl.
    rewrite address_eq_refl; simpl.
    unfold withdraw. 
    simpl.
    rewrite Hst.
    simpl.
    dc Eee idtac.
    { false. destruct_address_eq; try congruence.
      unfold miner_reward in Eee. lia. lia. }
    simpl.
    unfold send_or_call.
    rewrite address_eq_refl; simpl.
    assert (Hff: (caddr =? miner)%address = false).
    {
      lets H__: addr_ctr_neq caddr miner; eauto.
      specializes H__; eauto.
      eapply address_eq_ne; eauto.
    }
    rewrite Hff; simpl.
    rewrite address_eq_refl; simpl.
    assert (Hfu: (caddr =? h_usr)%address = false).
    {
      lets H__: addr_ctr_neq caddr h_usr; eauto.
      specializes H__; eauto.
      eapply address_eq_ne; eauto.
    }
    rewrite Hfu; simpl.
    rewrite address_eq_sym in Hfu.
    rewrite Hfu; simpl.
    asserts_rewrite (0 + env_account_balances s caddr <? 0 = false).
    {
      lets H__: Z.ltb_spec0 (0 + env_account_balances s caddr) 0.
      inverts H__; try (false; lia); auto.
    }
    match goal with
      H: _ |- context [?t1 >? ?t2] => asserts_rewrite (t1 >? t2 = false)
    end.
    {
      simpl.
      destruct_address_eq;try congruence.
      lia. lia.
    }
    simpl.
    lets Hn: addr_not_ctr_none Hrc h_usr_eoa.
    rewrite Hn.
    asserts_rewrite (address_is_contract h_usr = false).
    {
      unfolds in h_usr_eoa.
      destruct (address_is_contract h_usr); tryfalse; auto.
    }
    simpl.
    split.
    eauto.
    split.
    {
      unfolds.
      simpl.
      destruct_address_eq;try congruence.
      lia. lia.
    }
    {
      eexists. simpl. 
      splits.
      unfolds. simpl.
      rewrite address_eq_refl.
      rewrite deserialize_serialize.
      eauto.
      simpl. apply FMap.find_remove.
      simpl. auto.
    }
  Qed.         
  
  Lemma usr_wth_strat_drive:  
    forall (s:ChainState) (cstate: State) (tr: TransitionTrace miner s0 s),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = Some status_approved ->
      transition_reachable miner contract caddr s0 s ->
      exists s' tr', 
        stratDrive miner [h_usr; adm] honest_strat s0 s tr s' tr' /\ 
          funds s' caddr = 0 /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = None /\
              cs.(admin) = cstate.(admin). 
  Proof.
    introv Hcs Hapr Htrc.
    lets H__: usr_wth_transition_correct Hcs Hapr Htrc.
    protect addr_neq.
    destruct_and_split.
    exists x. 
    eexists.
    split.
    exists usr_call_withdraw. eexists. exists H.
    split.
    unfold honest_strat.
    unfold liqVerif. simpl.
    rewrite Hcs. rewrite Hapr.
    simpl; auto.
    eauto.
    split; auto.
    eexists. splits; eauto.
  Qed.

  Theorem fm_sat_strat_liquidity:
    forall (att_strat: strat miner [d_usr]),
      well_strat [d_usr] att_strat -> 
      strat_liquidity miner [h_usr; adm] honest_strat [d_usr] att_strat contract caddr s0.
  Proof.
    introv Hwstrat.
    eapply strat_liq_inst.
    lets H__: soundness; eauto.
    eapply H__; eauto; clear H__.
    
    { (* VC_R *)
      unfold VC_R; unfold liqVerif.
      introv Htrc.
      assert (Hrc: reachable cs).
      {
        eapply transition_reachable_impl_reachable in H_init; eauto.
      }
      assert (Hrth: reachable_through inist cs).
      {
        eapply transition_reachable_impl_reachable_through in H_init; eauto.
      }
      assert (Hectr: env_contracts cs cur_adr = Some (theCtr: WeakContract)).
      {
        unfolds in H_init.
        destructs H_init. 
        eapply reachable_through_contract_deployed; eauto.
      }
      lets H__: reachable_ex_cstate Hrc Hectr.
      destruct H__ as (st & Hst & Hor3 & Hadm).
      assert (Hinv: Inv cs cs).
      {
        unfold Inv; unfold liqVerif.
        unfold inv_func.
        split.
        - unfold theCtr, cur_adr, inist in Htrc; unfold liqVerif in Htrc.
          auto.
        - eexists; splits; eauto.
      }
      split; auto.
      eapply inv_var_def; eauto. 
    }

    { (* VC_B *)
      unfold VC_B. 
      unfold Var; unfold liqVerif.
      introv Hinv Hvfn Hmin.
      eapply min_zero in Hmin.
      rewrite Hmin in Hvfn.
      eapply min_bal_zero; eauto.
    }

    { (* VC_A *)
      unfold VC_A; unfold liqVerif.
      introv Hvar Hinv Hmsd.
      unfold Inv in Hinv; unfold liqVerif in Hinv.
      unfolds in Hinv.
      destruct Hinv as (Htrc & Hex).
      destruct Hex as (st & Hcs & Hor3 & Hadm).
      unfold inist in Hmsd.    
      lets H__: att_multi_strat_drive_preserves_status Hcs Htrc Hmsd Hwstrat.
      destruct H__ as (cs'0 & Hcs'0 & Hsteq & Hfmeq & Hadeq).
      split.
      -
        unfold Inv; unfold liqVerif.
        unfolds.
        split; auto.
        eexists; splits; eauto.
        + 
          rewrite Hfmeq.
          auto.
        +
          congruence.
      -
        lets H__: fm_eq_var_preserved_nmin Hcs Hsteq Hfmeq Hvar.
        auto.
    }

    { (* VC_U *)
      unfold VC_U; unfold liqVerif.
      introv Hinv Hvar Hnmin.  
      unfolds in Hinv.
      unfolds in Hinv.
      destruct Hinv as (Htrc & Hex).
      destruct Hex as (st & Hst & Hor3 & Hadm).
      destruct Hor3 as [Hnone | [Hreq | Hapr]].
      - 
        assert (Hane: address_neqb h_usr (admin st) = true).
        {
          rewrite Hadm. destructs addr_neq. 
          eapply adr_neq_reflect; eauto.
        }
        lets H__: usr_req_strat_drive tr Hst Hnone Htrc Hane.
        destruct H__ as (cs' & tr' & Hsd & Hfd & Hex).
        destruct Hex as (st' & Hst' & Hfm' & Hadm').
        assert (Htrc': transition_reachable miner contract caddr s0 cs').
        {
          eapply transition_reachable_stratDrive_transition_reachable; eauto.
        }
        do 2 eexists; splits; eauto.
        + unfold Inv. unfold inv_func.
          split; auto.
          eexists; split; eauto.
          split; eauto.
          congruence.
        + unfold Var. unfold var_func.
          unfold Var in Hvar; unfold liqVerif in Hvar.
          unfolds in Hvar.
          rewrite Hst'.
          rewrite Hst in Hvar.
          rewrite Hfm'. rewrite Hnone in Hvar.
          destruct (0 <? env_account_balances cs caddr) eqn: E.
          * inverts Hvar.
            simpl. eexists; split; eauto.
          * inverts Hvar.
            false. apply Hnmin. unfolds. unfold Ord. introv Hf. lia.
            
      - lets H__: adm_apr_strat_drive tr Hst Hreq Hadm Htrc.
        destruct H__ as (cs' & tr' & Hsd & Hfd & Hex).
        destruct Hex as (st' & Hst' & Hfm' & Hadm').
        assert (Htrc': transition_reachable miner contract caddr s0 cs').
        {
          eapply transition_reachable_stratDrive_transition_reachable; eauto.
        }
        do 2 eexists; splits; eauto.
        + unfold Inv. unfold inv_func.
          split; auto.
          eexists; split; eauto.
          split; eauto.
          congruence.
        + unfold Var. unfold var_func.
          unfold Var in Hvar; unfold liqVerif in Hvar.
          unfolds in Hvar.
          rewrite Hst'.
          rewrite Hst in Hvar.
          rewrite Hfm'. rewrite Hreq in Hvar.
          simpl. simpl in Hvar.
          inverts Hvar. eexists; splits; eauto.
          
      - lets H__: usr_wth_strat_drive tr Hst Hapr Htrc.
        destruct H__ as (cs' & tr' & Hsd & Hfd & Hex).
        destruct Hex as (st' & Hst' & Hfm' & Hadm').
        assert (Htrc': transition_reachable miner contract caddr s0 cs').
        {
          eapply transition_reachable_stratDrive_transition_reachable; eauto.
        }
        do 2 eexists; splits; eauto.
        + unfold Inv. unfold inv_func.
          split; auto.
          eexists; split; eauto.
          split; eauto.
          congruence.
        + unfold Var. unfold var_func.
          unfold Var in Hvar; unfold liqVerif in Hvar.
          unfolds in Hvar.
          rewrite Hst'.
          rewrite Hst in Hvar.
          rewrite Hfm'. rewrite Hapr in Hvar.
          simpl in Hvar. inverts Hvar.
          unfold funds in Hfd. rewrite Hfd.
          simpl.
          eexists; splits; eauto.
    }
  Qed. 

End Liquidity.

