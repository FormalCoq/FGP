(* this is my first time try to formalize sth by myself,
   so don't mind *)

Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Nat.

Inductive Constants (T : Set) : Set :=
  | Classify : Constants T -> T -> Constants T .

Inductive APIReType : Set :=
  | TEE_SUCCESS
  | TEE_ERROR_BAD_PARAMETERS
  | TEE_ERROR_OUT_OF_MEMORY
  | TEE_ERROR_ITEM_NOT_FOUND
  | TEE_ERROR_ACCESS_DENIED
  | TEE_ERROR_BUSY
  | TEE_ERROR_TARGET_DEAD.

Inductive ParaType : Set :=
  | TEE_PARAM_TYPE_NONE
  | TEE_PARAM_VALUE_INPUT
  | TEE_PARAM_VALUE_OUTPUT
  | TEE_PARAM_VALUE_INOUT
  | TEE_PARAM_MEMREF_INPUT
  | TEE_PARAM_MEMREF_OUTPUT
  | TEE_PARAM_MEMREF_INOUT.

Inductive LogType : Set :=
  | TEE_LOGIN_PUBLIC
  | TEE_LOGIN_USER
  | TEE_LOGIN_GROUP
  | TEE_LOGIN_APPLICATION
  | TEE_LOGIN_APPLICATION_USER
  | TEE_LOGIN_APPLICATION_GROUP.

Inductive MemAccRight : Set :=
  | TEE_MEMORY_ACCESS_READ
  | TEE_MEMORY_ACCESS_WRITE
  | TEE_MEMORY_ACCESS_ANY_OWNER.

(* because they're independent type
   so define them with their own inductive *)
Inductive uint32_t : Set :=
  | uint32.
Inductive uint16_t : Set :=
  | uint16.
Inductive uint8_t : Set :=
  | uint8.

Inductive int32_t : Set :=
  | int32.
Inductive int16_t : Set :=
  | int16.
Inductive int8_t : Set :=
  | int8.

(* the operations of TA interface *)
Inductive GP_TEE_TA_Interface : Set :=
  | TA_CreateEntryPoint
  | TA_DestroyEntryPoint
  | TA_OpenSessionEntryPoint
  | TA_CloseSessionEntryPoint
  | TA_InvokeCommandEntryPoint.

Variable TEE_Result : uint32_t.
Variable TEEC_Result : uint32_t.

Record TEE_UUID : Set := {
  timeLow : option uint32_t;
  timeMid : option uint16_t;
  timeHiAndVersion : option uint16_t;
  clockSeqAndNode : option (list uint8_t);
}.

Record TEE_Identity : Set := {
  login : option uint32_t;
  uuid : option TEE_UUID;
}.

Record value : Set := {
  a : uint32_t;
  b : uint32_t;
}.

Record memref : Set := {
  buffer : list nat;   (* waiting for dealing, how to show void* *)
  size : uint32_t;
}.

Record TEE_Param : Set := {
  v : value;
  m : memref;
}.

Record TEE_Session : Set := {
  ID : option nat;
}.

Record State : Set := {
  (* maybe one more session *)
  session : list TEE_Session;
  trace : option GP_TEE_TA_Interface;
  (* after opensession, this should be created,
     and never be changed before closesession*)
  ident : option TEE_Identity;
  re : option APIReType
}.

Parameter Session_count : option nat.

Definition Value_GP2nat (ops : GP_TEE_TA_Interface) : nat := 
  match ops with
   | TA_CreateEntryPoint => 1
   | TA_DestroyEntryPoint => 2
   | TA_OpenSessionEntryPoint => 3
   | TA_CloseSessionEntryPoint => 4
   | TA_InvokeCommandEntryPoint => 5
  end.

Definition State_Session_count : option nat := 
  match Session_count with 
   | None => let Session_count := Some 0 in Session_count
   | Some n => let Session_count := (Some (S n)) in Session_count
  end.

Definition State_session : TEE_Session := 
  Build_TEE_Session (Some 1).

(* the reason why I delay one state,
   because it means just entering that state and nothing be done,
   only ops is changed *)
(* used to check the state trace*)
Definition State_trace (ops : GP_TEE_TA_Interface) (s : State) : State :=
  match trace s with
   (* only TA_CreateEntryPoint is vaild *)
   | None => if   eqb (Value_GP2nat ops) (Value_GP2nat TA_CreateEntryPoint)
             then Build_State (cons State_session nil)
                              (Some TA_CreateEntryPoint) None
                              (Some TEE_SUCCESS)
             else Build_State (cons State_session nil) 
                              None None
                              (Some TEE_ERROR_BAD_PARAMETERS)
   (* all of the ops type are vaild except itself *)
   | Some TA_CreateEntryPoint =>
             if   eqb (Value_GP2nat ops) (Value_GP2nat TA_CreateEntryPoint)
             then Build_State (cons State_session nil)
                              None None
                              (Some TEE_ERROR_BAD_PARAMETERS)
             else Build_State (cons State_session nil)
                              (Some TA_CreateEntryPoint) None
                              (Some TEE_SUCCESS)
   (* if the type of ops is TA_DestroyEntryPoint
      there should be no next type no session list and always success *)
   | Some TA_DestroyEntryPoint => Build_State nil 
                                              None None 
                                              (Some TEE_SUCCESS)
   (* all of the ops type are vaild except TA_CreateEntryPoint *)
   | Some TA_OpenSessionEntryPoint => 
             if   eqb (Value_GP2nat ops) (Value_GP2nat TA_CreateEntryPoint)
             then Build_State (cons State_session nil)
                              None None
                              (Some TEE_ERROR_BAD_PARAMETERS)
             else Build_State (cons State_session nil)
                              (Some ops) (ident s)
                              (Some TEE_SUCCESS)
   (* all of the ops type are vaild except TA_CreateEntryPoint *)
   | Some TA_CloseSessionEntryPoint => 
             if   eqb (Value_GP2nat ops) (Value_GP2nat TA_CreateEntryPoint)
             then Build_State (cons State_session nil)
                              None None
                              (Some TEE_ERROR_BAD_PARAMETERS)
             else Build_State (cons State_session nil)
                              (Some ops) (ident s)
                              (Some TEE_SUCCESS)
   (* all of the ops type are vaild except TA_CreateEntryPoint *)
   | Some TA_InvokeCommandEntryPoint => 
             if   eqb (Value_GP2nat ops) (Value_GP2nat TA_CreateEntryPoint)
             then Build_State (cons State_session nil)
                              None None
                              (Some TEE_ERROR_BAD_PARAMETERS)
             else Build_State (cons State_session nil)
                              (Some ops) (ident s)
                              (Some TEE_SUCCESS)
  end.

Definition State_Denote (ops : GP_TEE_TA_Interface) (s : State) : State := State_trace ops s.

(* the denotational of every operation should be seperated with its state, I think *)
(* the operations denotational should match the GP API *)
Definition TA_CreateEntryPoint_Denote (s : State) : State :=
  let re :=  in
  Build_State (cons (Build_State (Some 1)) nil)
              (Some TA_CreateEntryPoint)
              (Build_State ) re.

Definition TA_CreateEntryPoint_Denote : option APIReType :=
  let s := State_Denote TA_CreateEntryPoint (Build_State  None None) in re s.

Definition TA_CreateEntryPoint_Denote : option APIReType :=
  let s := State_Denote TA_CreateEntryPoint (Build_State  None None) in re s.

Definition TA_CreateEntryPoint_Denote : option APIReType :=
  let s := State_Denote TA_CreateEntryPoint (Build_State  None None) in re s.

Definition TA_CreateEntryPoint_Denote : option APIReType :=
  let s := State_Denote TA_CreateEntryPoint (Build_State  None None) in re s.

(* 还需要一个下一个状态装换 *)

(* the denotational of TA Interface *)
Definition GP_TEE_TA_Interface_Denote (ops : GP_TEE_TA_Interface) (s : State) : option APIReType :=
  match ops with
   | TA_CreateEntryPoint => TA_CreateEntryPoint_Denote
   | TA_DestroyEntryPoint => (s, Some TEE_SUCCESS)
   | TA_OpenSessionEntryPoint => (s, Some TEE_SUCCESS)
   | TA_CloseSessionEntryPoint => (s, Some TEE_SUCCESS)
   | TA_InvokeCommandEntryPoint => (s, Some TEE_SUCCESS)
  end.

(* the former ops before Invoke must be successful opensession *)
Inductive TA_TIVK_order (ops : GP_TEE_TA_Interface) : State -> Set:=
  | order_TIVK : forall s, Some TEE_SUCCESS = (re s) -> Some TA_OpenSessionEntryPoint = (trace s) -> TA_TIVK_order ops s.

(* the length of the input paramter *)
Theorem paramterLength : .
Proof.

Save.

(* check the session ID *)
Theorem sessionID_check : .
Proof.

Save.

(* the final operation *)
Theorem final_operation_state : .
Proof.

Save.












