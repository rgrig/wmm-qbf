(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2013-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

open Printf

(* Should be put in a bell library *)
let string_of_annot_list a = String.concat "," a
let string_of_labels a = Label.Set.pp_str "," Misc.identity a

(* Who am i ? *)
let arch = Archs.lisa

type gpr_reg = int
[@@deriving show]

type reg =
  | GPRreg of gpr_reg
  | Symbolic_reg of string
[@@deriving show]

let reg_compare = Pervasives.compare

let symb_reg_name = function
  | Symbolic_reg s -> Some s
  | _ -> None

let parse_reg s =
  let len = String.length s in
  assert (len > 0) ;
  match s.[0] with
  | 'r' ->
      begin try
        let rem = String.sub s 1 (len-1) in
        Some (GPRreg (int_of_string rem))
      with _ -> None end
  | _ -> None

(****************)
(* Barriers     *)
(****************)

type barrier =
 | Fence of string list * (Label.Set.t * Label.Set.t) option
 (* list of annotations, optional sets of labels*)

(* jade: i'm guessing this is to give one possible example fence? picking this one *)
let all_kinds_of_barriers =  [ Fence ([], None);]

let show_barrier b = match b with
  | Fence(s, None) ->
      sprintf "Fence(%s)" (string_of_annot_list s)
  | Fence(s, Some(s1,s2)) ->
      sprintf "Fence(%s)(%s X %s)"
        (string_of_annot_list s)
        (string_of_labels s1)
        (string_of_labels s2)

let pp_barrier f b = Format.fprintf f "%s" (show_barrier b)

let barrier_compare = Pervasives.compare

(* For barrier instructions, MUST be the same as parsed *)
let pp_fence_ins = function
  | Fence (s,None) ->
      sprintf "f[%s]" (string_of_annot_list s)
  | Fence(s, Some(s1,s2)) ->
      sprintf "f[%s] {%s} {%s}"
        (string_of_annot_list s)
        (string_of_labels s1)
        (string_of_labels s2)


(****************)
(* Instructions *)
(****************)

type lbl = Label.t
[@@deriving show]


type 'k reg_or_imm =
| Regi of reg
| Imm of 'k
[@@deriving show]

let reg_or_imm_tr f = function
  | Imm k -> Imm (f k)
  | Regi _ as keep -> keep

let string_of_reg_or_imm r = match r with
  | Regi r -> show_reg r
  | Imm r -> sprintf "%d" r

open Constant

type reg_or_addr =
  | Rega of reg  (* address given in register *)
  | Abs of SymbConstant.v (* address given as a constant *)
[@@deriving show]

let pp_abs = function
  | Symbolic s -> s
  | Concrete i -> string_of_int i

let string_of_reg_or_addr r = match r with
  | Rega r -> show_reg r
  | Abs r -> pp_abs r

type 'k imm_or_addr_or_reg =
  | IAR_roa of reg_or_addr
  | IAR_imm of 'k
[@@deriving show]

let imm_or_addr_or_reg_tr f = function
  | IAR_roa _ as keep -> keep
  | IAR_imm k -> IAR_imm (f k)

let show_iar iar = match iar with
  | IAR_roa roa -> string_of_reg_or_addr roa
  | IAR_imm i -> sprintf "%d" i

let pp_iar f i = Format.fprintf f "%s" (show_iar i)
               
type 'k addr_op =
| Addr_op_atom of reg_or_addr
| Addr_op_add of reg_or_addr * 'k reg_or_imm
                                  [@@deriving show]
               
let addr_op_tr f = function
  | Addr_op_add (r,k) -> Addr_op_add (r,reg_or_imm_tr f k)
  | Addr_op_atom _ as keep -> keep

let show_addr_op a = match a with
  | Addr_op_atom roa -> string_of_reg_or_addr roa
  | Addr_op_add(roa,roi) -> sprintf "%s+%s" (string_of_reg_or_addr roa)
    (string_of_reg_or_imm roi)
                          
type op_t =
  | Add | Xor | And | Eq | Neq
[@@deriving show]

type 'k op =
  | RAI of 'k imm_or_addr_or_reg
  | OP of op_t * 'k imm_or_addr_or_reg * 'k imm_or_addr_or_reg
[@@deriving show]

let r_in_op =
  let in_addr r = function
    | IAR_roa (Rega ra) -> reg_compare r ra = 0
    | IAR_roa (Abs _)
    | IAR_imm _ -> false in
  fun r x -> match x with
  | RAI a -> in_addr r a
  | OP (_,x,y) ->
      in_addr r x || in_addr r y

let op_tr f = function
  | RAI (iar) ->
      RAI (imm_or_addr_or_reg_tr f iar)
  | OP (op,iar1,iar2) ->
      OP (op,imm_or_addr_or_reg_tr f iar1,imm_or_addr_or_reg_tr f iar2)


let show_op = function
  | RAI(iar) -> sprintf "%s" (show_iar iar)
  | OP(Add,x,i) -> sprintf "(add %s %s)" (show_iar x) (show_iar i)
  | OP(Xor,x,i) -> sprintf "(xor %s %s)" (show_iar x) (show_iar i)
  | OP(And,x,i) -> sprintf "(and %s %s)" (show_iar x) (show_iar i)
  | OP(Eq,x,y) -> sprintf "(eq %s %s)" (show_iar x) (show_iar y)
  | OP(Neq,x,y) -> sprintf "(neq %s %s)" (show_iar x) (show_iar y)

type 'k kinstruction =
| Pld of reg * 'k addr_op * string list
| Pst of 'k addr_op * 'k reg_or_imm * string list
| Pfence of barrier
| Pcall of string
| Prmw of reg * 'k op * 'k addr_op * string list
| Pbranch of reg option * lbl * string list
| Pmov of reg * 'k op
                   [@@deriving show]

let instruction_tr f = function
  | Pld (r,x,s) -> Pld (r,addr_op_tr f x,s)
  | Pst (x,ri,s) -> Pst (addr_op_tr f x,reg_or_imm_tr f ri,s)
  | Pfence _ as i -> i
  | Prmw (r,op,x,s) -> Prmw (r,op_tr f op,addr_op_tr f x,s)
  | Pbranch _|Pcall _ as i -> i
  | Pmov (r,op) -> Pmov (r,op_tr f op)

type instruction = int kinstruction
type parsedInstruction = MetaConst.k kinstruction

let pp_instruction f k = pp_kinstruction (fun f d -> Format.fprintf f "%d" d) f k
let pp_parsedInstruction f k = pp_kinstruction MetaConst.pp_k f k
                       
(* from GPU_PTXBase *)

include Pseudo.Make
    (struct
      type ins = instruction [@@deriving show]
      type pins = parsedInstruction [@@deriving show]
      type reg_arg = reg [@@deriving show]

      let parsed_tr i = instruction_tr MetaConst.as_int i

      let get_naccesses = function
        | Pld _
        | Pst _  -> 1
        | _ -> 0

      (* We do have instructions with labels... *)
      let fold_labels k f = function
        | Pbranch (_,lbl,_) -> f k lbl
        | _ -> k

      let map_labels f = function
        | Pbranch(c,lbl,s) -> Pbranch(c,f lbl,s)
        | ins -> ins

     end)

let dump_instruction i = match i with
| Pld(r, addr_op, s) -> sprintf "r[%s] %s %s"
      (string_of_annot_list s)
      (show_reg r)
      (show_addr_op addr_op)

| Pst(addr_op,roi,s) -> sprintf "w[%s] %s %s"
      (string_of_annot_list s)
      (show_addr_op addr_op)
      (string_of_reg_or_imm roi)

| Prmw(r,op,x,s) -> sprintf "rmw[%s] %s %s %s"
      (string_of_annot_list s)
      (show_reg r)
      (show_op op)
      (show_addr_op x)

| Pfence f -> pp_fence_ins f

| Pcall s -> sprintf "call[%s]" s

| Pbranch(Some r,l,s) -> sprintf "b[%s] %s %s"
      (string_of_annot_list s)
      (show_reg r)
      l

| Pbranch(None,l,s) -> sprintf "b[%s] %s"
      (string_of_annot_list s)
      l

| Pmov(r,op) -> sprintf "mov %s %s"
      (show_reg r)
      (show_op op)

let fold_regs (f_reg,f_sreg) =
  let fold_reg reg (y_reg,y_sreg) = match reg with
    | GPRreg _ -> f_reg reg y_reg,y_sreg
    | Symbolic_reg reg -> y_reg,f_sreg reg y_sreg
  in
  let fold_roa roa c = match roa with
    | Rega r -> fold_reg r c
    | Abs _ -> c
  in
  let fold_roi roi c = match roi with
    | Imm _ -> c
    | Regi r -> fold_reg r c
  in
  let fold_iar iar c = match iar with
    | IAR_roa roa -> fold_roa roa c
    | IAR_imm _ -> c
  in
  let fold_addr_op ao c = match ao with
    | Addr_op_atom roa -> fold_roa roa c
    | Addr_op_add(roa,roi) -> fold_roa roa (fold_roi roi c)
  in
  let fold_op op c = match op with
    | RAI(i) -> fold_iar i c
    | OP(_,x,i) -> fold_iar x (fold_iar i c)
  in
  let fold_ins (_y_reg,_y_sreg as c) ins =
    begin match ins with
    | Pld(r, addr_op, _) -> fold_reg r (fold_addr_op addr_op c)
    | Pst(addr_op,roi,_) -> fold_addr_op addr_op (fold_roi roi c)
    | Pfence _|Pcall _|Pbranch (None,_,_) -> c
    | Prmw(r,op,_,_) -> fold_reg r (fold_op op c)
    | Pbranch(Some r,_,_) -> fold_reg r c
    | Pmov(r,op) -> fold_reg r (fold_op op c)
    end
  in fold_ins

let map_regs f_reg f_symb =

  let map_reg reg = match reg with
  | GPRreg _ -> f_reg reg
  | Symbolic_reg reg -> f_symb reg in

  let map_roa roa = match roa with
    | Abs _ -> roa
    | Rega r -> Rega(map_reg r)
  in
  let map_roi roi = match roi with
    | Imm _ -> roi
    | Regi r -> Regi(map_reg r)
  in
  let map_iar iar = match iar with
    | IAR_imm _ -> iar
    | IAR_roa roa -> IAR_roa(map_roa roa)
  in
  let map_addr_op ao = match ao with
    | Addr_op_atom roa -> Addr_op_atom(map_roa roa)
    | Addr_op_add(roa,roi) -> Addr_op_add(map_roa roa,map_roi roi)
  in
  let map_op op = match op with
    | RAI(i) -> RAI(map_iar i)
    | OP(op,x,i) -> OP(op,map_iar x, map_iar i)
  in
  let map_ins ins = begin match ins with
    | Pld(r,addr_op,s) -> Pld(map_reg r, map_addr_op addr_op, s)
    | Pst(addr_op,roi,s) -> Pst(map_addr_op addr_op, map_roi roi, s)
    | Prmw(r,op,x,s) -> Prmw(map_reg r,map_op op, map_addr_op x, s)
    | Pbranch(Some r,lbl,s) -> Pbranch(Some (map_reg r),lbl,s)
    | Pfence _|Pcall _|Pbranch (None,_,_) -> ins
    | Pmov(r,op) -> Pmov(map_reg r,map_op op)
  end in
  map_ins

(* Seems to work for other architectures *)

let norm_ins ins = ins


let fold_addrs f =
 let fold_roa roa c = match roa with
  | Rega _ -> c
  | Abs a -> f a c
 in
 let fold_iar iar c = match iar with
  | IAR_roa roa -> fold_roa roa c
  | IAR_imm _ -> c
 in
 let fold_ao ao c = match ao with
   | Addr_op_atom roa
   | Addr_op_add (roa,_) ->
       fold_roa roa c
  in
  let fold_op op c = match op with
    | RAI(i) -> fold_iar i c
    | OP(_,x,i) -> fold_iar x (fold_iar i c)
  in
  fun c ins -> match ins with
  | Pbranch _ | Pfence _|Pcall _ -> c
  | Pld (_,ao,_) | Pst (ao,_,_) -> fold_ao ao c
  | Prmw (_,op,x,_) -> fold_op op (fold_ao x c)
  | Pmov (_,op) -> fold_op op c

let pp_instruction _m ins = dump_instruction ins

(* 100 registers are probably enough *)
let allowed_for_symb = List.map (fun r ->  GPRreg r) (Misc.interval 0 100)


let _get_reg_list _ins = ([], [])


(* unimplemented so far, will implement if needed*)
let get_macro _name = Warn.fatal "Bell get_macro has not been implemented"

let is_data _reg _ins = Warn.fatal "Bell is_data has not been implemented"

let map_addrs _f _ins = Warn.fatal "Bell map_addrs has not been implemented"

let get_next _ins = Warn.fatal "Bell get_next not implemented"

let set_shared _i = Warn.fatal "Bell set_shared has not been implemented"

let set_global _i = Warn.fatal "Bell set_global has not been implemented"

let get_reg_list _i = Warn.fatal "Bell get_reg_list has not been implemented"

(* Annotations *)
let get_id_and_list i = match i with
| Pld(_,_,s) -> (BellName.r,s)
| Pst(_,_,s) -> (BellName.w,s)
| Pfence (Fence (s, _)) -> (BellName.f,s)
| Prmw(_,_,_,s) -> (BellName.rmw,s)
| Pbranch(_,_,s) -> (BellName.b,s)
| Pcall s -> (BellName.call,[s])
| Pmov _ -> raise Not_found

let get_from_and_to_labels b = match b with
| Fence (_, a) -> a

let set_list i al = match i with
| Pld (a1,a2,_) -> Pld (a1,a2,al)
| Pst (a1,a2,_) -> Pst (a1,a2,al)
| Pfence (Fence (_,a2)) -> Pfence (Fence (al,a2))
| Prmw(a1,a2,a3,_) -> Prmw(a1,a2,a3,al)
| Pbranch(a1,a2,_) -> Pbranch(a1,a2,al)
| Pcall _ ->
    begin match al with
    | [] -> i
    | s::_ -> Pcall s
    end
| Pmov _ as i -> i

let tr_compat = function
  | Pcall "sync" -> Pfence (Fence (["sync";],None))
  | i -> i
