(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2010-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

(** Constants in code *)

type v =
  | Concrete of int
  | Symbolic of string
[@@ deriving show]

module type S =
  sig
    val pp : bool -> v -> string (* true -> hexa *)

    val pp_v  : Format.formatter -> v -> Ppx_deriving_runtime.unit
    val show_v  : v -> string

    val compare : v -> v -> int

    val intToV  : int -> v 
    val nameToV  : string -> v
  end
