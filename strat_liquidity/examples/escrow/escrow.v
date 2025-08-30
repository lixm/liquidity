
Require Export Blockchain.
Require Export Serializable.
Require Export Extras.
Require Export BuildUtils.
Require Export RecordUpdate.
Require Export Automation.
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

Context `{caddr : Address} `{miner : Address}.

Variable seller_adr : Address.
Variable buyer_adr : Address.
Variable arbitrator_adr : Address.  

Section InstrumentEscrow.

  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Local Open Scope Z.

  Inductive EscrowPhase :=
  | AWAITING_SHIPMENT
  | AWAITING_ACCEPTANCE
  | COMPLETED
  | DISPUTED.

  (** Storage state of the contract *)
  Record State :=
    build_state {
        buyer : Address;         
        seller : Address;         
        arbitrator : Address;  
        currentPhase : EscrowPhase;   
        depositAmount : Amount; 
        itemAccepted : bool;  
      }.

  Record Setup :=
    build_setup {
        setup_seller : Address;
        setup_arbitrator : Address
      }.

  Instance state_settable : Settable State :=
    settable! build_state
    <buyer; seller; arbitrator; currentPhase; depositAmount; itemAccepted>.

  Instance setup_settable : Settable Setup :=
    settable! build_setup
    <setup_seller; setup_arbitrator>.

  Section Serialization.
    Global Instance EscrowPhase_serializable : Serializable EscrowPhase :=
      Derive Serializable
        EscrowPhase_rect<AWAITING_SHIPMENT, AWAITING_ACCEPTANCE, COMPLETED, DISPUTED>.

    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.
  End Serialization.

  Inductive Msg :=
  | MarkAsShipped
  | AcceptItem
  | RejectItem
  | Arbitrate (buyerWins : bool).

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<MarkAsShipped, AcceptItem, RejectItem, Arbitrate>.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  (**  initialization function *)
  (** 
         constructor(address _seller, address _arbitrator) payable
           - buyer = msg.seller
           - seller = _seller
           - depositAmount = msg.value
           - arbitrator = _arbitrator
           - currentState = AWAITING_SHIPMENT
   *)
  Definition init
    (chain : Chain)
    (ctx : ContractCallContext)
    (setup : Setup)
    : result State Error :=
    let msg_sender := ctx_from ctx in
    let msg_value  := ctx_amount ctx in
    if (msg_value >? 0)%Z && 
         (msg_sender =? buyer_adr)%address &&
         address_not_contract seller_adr &&
         address_not_contract buyer_adr &&
         address_not_contract arbitrator_adr && 
         address_neqb seller_adr buyer_adr && 
         address_neqb seller_adr arbitrator_adr &&
         address_neqb buyer_adr arbitrator_adr 
    then 
      Ok (
        build_state
          buyer_adr  
          seller_adr  
          arbitrator_adr 
          AWAITING_SHIPMENT   (* currentPhase = AWAITING_SHIPMENT *)
          msg_value                        (* depositAmount = msg.value *)
          false                                  (* itemAccepted = false *)
        )
    else
      Err default_error.

  Definition require_phase (st : State) (ph : EscrowPhase) : bool :=
    match st.(currentPhase), ph with
    | AWAITING_SHIPMENT, AWAITING_SHIPMENT => true
    | AWAITING_ACCEPTANCE, AWAITING_ACCEPTANCE => true
    | COMPLETED, COMPLETED => true
    | DISPUTED, DISPUTED => true
    | _, _ => false
    end.

  Definition require_sender (ctx : ContractCallContext) (addr : Address) : bool :=
    address_eqb (ctx_from ctx) addr.

  Definition require_zero (ctx : ContractCallContext) : bool :=
    (ctx_amount ctx =? 0) .

  Definition require_not_self_call (ctx : ContractCallContext) : bool :=
    (address_neqb (ctx.(ctx_from))  (ctx.(ctx_contract_address))).

  (***********************************************************)
  (** ** Seller marks that the item is shipped                              *)
  (***********************************************************)
  Definition markAsShipped
    (chain : Chain)
    (ctx : ContractCallContext)
    (st : State)
    : result (State * list ActionBody) Error :=
    if (require_phase st AWAITING_SHIPMENT) && (require_sender ctx st.(seller))
    then
      let new_st := st <| currentPhase := AWAITING_ACCEPTANCE |> in
      Ok (new_st, [])
    else
      Err default_error.

  (***********************************************************)
  (** ** buyer validates and accepts the item                              *)
  (***********************************************************)
  Definition acceptItem
    (chain : Chain)
    (ctx : ContractCallContext)
    (st : State)
    : result (State * list ActionBody) Error :=
    if (require_phase st AWAITING_ACCEPTANCE) && (require_sender ctx st.(buyer))
    then
      (* transfer funds to the seller  *)
      let actions := [ act_transfer st.(seller) st.(depositAmount) ] in
      let new_st := st <| itemAccepted := true |>
                                <| currentPhase := COMPLETED |>
                                <| depositAmount := 0 |>
      in
      Ok (new_st, actions)
    else
      Err default_error.

  (***********************************************************)
  (** ** trigger dispute                                                                   *)
  (***********************************************************)
  Definition rejectItem
    (chain : Chain)
    (ctx : ContractCallContext)
    (st : State)
    : result (State * list ActionBody) Error :=
    if (require_phase st AWAITING_ACCEPTANCE ||
          require_phase st AWAITING_SHIPMENT) &&
         (require_sender ctx st.(seller) ||
            require_sender ctx st.(buyer))
    then
      (** currentPhase = DISPUTED; *)
      let new_st := st <| currentPhase := DISPUTED |> in
      Ok (new_st, [])
    else
      Err default_error.

  (***********************************************************)
  (** ** arbitrator resolves dispute                                              *)
  (***********************************************************)
  Definition arbitrate
    (chain : Chain)
    (ctx : ContractCallContext)
    (st : State)
    (buyerWins : bool)
    : result (State * list ActionBody) Error :=
    if (require_phase st DISPUTED) && (require_sender ctx st.(arbitrator))
    then
      (** if buyer wins then transfer to buyer; else transfer to seller. *)
      let to_addr :=
        if buyerWins then st.(buyer) else st.(seller) in
      let actions := [ act_transfer to_addr st.(depositAmount) ] in
      let new_st := st <| currentPhase := COMPLETED |><| depositAmount := 0 |> in
      Ok (new_st, actions)
    else
      Err default_error.

  (***********************************************************)
  (** ** message-dispatching function of the contract               *)
  (***********************************************************)
  Definition receive
    (chain : Chain)
    (ctx : ContractCallContext)
    (st : State)
    (msg : option Msg)
    : result (State * list ActionBody) Error :=
    if require_zero ctx && require_not_self_call ctx then
      match msg with
      | Some MarkAsShipped => markAsShipped chain ctx st
      | Some AcceptItem => acceptItem chain ctx st
      | Some RejectItem => rejectItem chain ctx st
      | Some (Arbitrate bWins) => arbitrate chain ctx st bWins
      | None => Err default_error 
      end
    else
      Err default_error. 


  (***********************************************************)
  (**    overall contract definition                                                 *)
  (***********************************************************)
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End InstrumentEscrow.
