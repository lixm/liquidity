
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

(* address of the honest user *)
Variable h_usr : Address.
(* address of the dishonest user *) 
Variable d_usr : Address.

(* Variable adm : Address. *)

Definition byte := Z. 

Theorem eq_bytes_dec (lb1 lb2: list byte): {lb1 = lb2} + {lb1 <> lb2}.
  repeat (decide equality).
Defined.

Class SHA3 :=
  build_sha3 {        
      sha3 : list byte -> list byte;
      collision_resistance :
      forall p1 p2, sha3 p1 = sha3 p2 -> p1 = p2; 
    }. 

Section Honeypot.
  
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Local Open Scope Z.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Inductive Msg :=
  | SetPass (h : list byte)
  | GetGift (pass : list byte)
  | LockPass (h : list byte).

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<SetPass, GetGift, LockPass>.

  Record State :=
    build_state {
        passLocked : bool;
        hashPass : list byte;
        balance : Z
      }.

  Record Setup :=
    build_setup {
        setup_passLocked : bool
      }.

  Instance state_settable : Settable State :=
    settable! build_state
    <passLocked; hashPass; balance>.

  Instance setup_settable : Settable Setup :=
    settable! build_setup
    <setup_passLocked>.


  Section Serialization.
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.
  End Serialization.

  (* initialization of contract *)
  Definition init
    (chain : Chain)
    (ctx : ContractCallContext)
    (setup : Setup)
    : result State Error :=
    Ok (build_state false [0] ctx.(ctx_amount)). 

  Definition one_ether : Z := 1.

  Definition require_zero (ctx : ContractCallContext) : bool :=
    (ctx_amount ctx =? 0) .

  (* fallback method *)
  Definition fallback_handler
    (ctx : ContractCallContext)
    (st : State)
    : State :=
    st <| balance := st.(balance) + ctx.(ctx_amount) |>.

  (* update the password if the password has not been locked *) 
  Definition setPass
    (ctx : ContractCallContext)
    (st : State)
    (hash : list byte)
    : result (State * list ActionBody) Error :=
    if (negb st.(passLocked)) && (ctx.(ctx_amount) >=? one_ether)
    then
      Ok ( st <| hashPass := hash|> <| balance  := st.(balance) + ctx.(ctx_amount) |>, [])
    else
      Ok ( st <| balance  := st.(balance) + ctx.(ctx_amount) |>, []).

  (* get the funds in the contract *)
  Definition getGift `{SHA3}
    (ctx : ContractCallContext)
    (st : State)
    (pass : list byte)
    : result (State * list ActionBody) Error :=
    if (require_zero ctx) then
      if (eq_bytes_dec st.(hashPass) (sha3 pass))
      then
        let amt := st.(balance) in
        Ok ( st <| balance := 0 |> , [ act_transfer (ctx_from ctx) amt ] )
      else
        Err default_error
    else
      Err default_error.

  (* lock the current password *) 
  Definition lockPass
    (ctx : ContractCallContext)
    (st : State)
    (hash : list byte)
    : result (State * list ActionBody) Error :=
    if (require_zero ctx) then
      if eq_bytes_dec hash st.(hashPass) 
      then Ok (st <| passLocked := true |>, [])
      else Err default_error
    else
      Err default_error.

  Definition receive `{SHA3}
    (chain : Chain)
    (ctx : ContractCallContext)
    (st : State)
    (msg : option Msg)
    : result (State * list ActionBody) Error :=
    match msg with
    | Some (SetPass h) =>
        setPass ctx st h
    | Some (GetGift p) =>
        getGift ctx st p
    | Some (LockPass h) =>
        lockPass ctx st h
    | None =>
        let new_st := fallback_handler ctx st in
        Ok (new_st, [])
    end.

  Definition contract `{SHA3} : Contract Setup Msg State Error :=
    build_contract init receive.
  
End Honeypot.
