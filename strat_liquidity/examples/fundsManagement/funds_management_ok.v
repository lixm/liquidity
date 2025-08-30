
Require Export Blockchain.
Require Export Serializable.
Require Export Extras.
Require Export BuildUtils.
Require Export RecordUpdate.
Require Export Automation.
Require Export Containers.
Require Export ContractCommon.
Require Export ResultMonad.
Require Export ChainedList.
Require Export ModelBase.
Require Export StratModel.
Require Export ProofLib.

From Coq Require Export List.
From Coq Require Export Bool.
From Coq Require Export ZArith.
From Coq Require Export Arith.
From Coq Require Export String.
Export ListNotations.
Require Export Lia.
Export RecordSetNotations.

Require Export LibTactics. 

Context `{caddr : Address} `{miner : Address}.

Variable zero_addr : Address.

Variable h_usr : Address.
Variable d_usr : Address.
Variable adm : Address.

Section FundsManagement.
  
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Local Open Scope Z.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Definition bytes := N. 

  Definition bytes32 := N.

  Inductive Msg :=
  | ReqWithdrawal 
  | ProcessReq (a: Address) (b : bool)
  | Withdraw. 

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<ReqWithdrawal, ProcessReq, Withdraw>. 
  
  Record State :=
    build_state {
        status : (FMap Address nat);
        admin : Address 
      }.

  Definition status_requested := 1%nat.
  Definition status_approved := 2%nat. 

  Record Setup :=
    build_setup {
        setup_status : FMap Address nat; 
        setup_admin : Address
      }.

  Instance state_settable : Settable State :=
    settable! build_state
    <status; admin>. 

  Instance setup_settable : Settable Setup :=
    settable! build_setup
    <setup_status; setup_admin>.


  Section Serialization.
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.
  End Serialization.

  Definition init 
    (chain : Chain)
    (ctx : ContractCallContext)
    (setup : Setup)
    : result State Error :=
      Ok (build_state FMap.empty adm). 
  
  Definition reqWithdrawal 
    (ctx: ContractCallContext)
    (st : State) 
    : result (State * list ActionBody) Error :=
    if address_neqb ctx.(ctx_origin) st.(admin) then 
      match FMap.find ctx.(ctx_origin) st.(status) with
        Some _ => Err default_error
      | None => Ok (st <| status := FMap.update ctx.(ctx_origin) (Some status_requested) st.(status) |>, []) 
      end
    else
      Err default_error.

  Definition processReq
    (ctx : ContractCallContext)
    (st : State)
    (a: Address)
    (b : bool)
    : result (State * list ActionBody) Error :=
    match FMap.find a st.(status) with
      Some n => 
        if address_eqb ctx.(ctx_origin) st.(admin)
           && beq_nat n status_requested then 
          if b then
            Ok (st <| status := FMap.update a (Some status_approved) st.(status) |>, []) 
          else
            Ok (st <| status := FMap.update a None st.(status) |>, [])  
        else
          Err default_error
    | None => Err default_error
    end.

  Definition withdraw
    (ctx : ContractCallContext)
    (st : State)
    : result (State * list ActionBody) Error :=
    match FMap.find ctx.(ctx_origin) st.(status) with
      Some n => 
        if beq_nat n status_approved then 
          Ok (st <| status := FMap.update ctx.(ctx_origin) None st.(status) |>, 
                  [ act_transfer ctx.(ctx_origin) ctx.(ctx_contract_balance) ])
        else
          Err default_error
    | None => Err default_error
    end.

  Definition receive
    (chain : Chain)
    (ctx : ContractCallContext)
    (st : State)
    (msg : option Msg)
    : result (State * list ActionBody) Error :=
    if address_eqb ctx.(ctx_origin) ctx.(ctx_from) then 
      match msg with
      | Some ReqWithdrawal =>
          reqWithdrawal ctx st 
      | Some (ProcessReq a b) => 
          processReq ctx st a b 
      | Some Withdraw => 
          withdraw ctx st
      | None => Ok (st, []) 
      end
    else
      Err default_error.
  
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End FundsManagement. 

