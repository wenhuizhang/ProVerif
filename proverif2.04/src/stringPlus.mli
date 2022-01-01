(*************************************************************
 *                                                           *
 *  Cryptographic protocol verifier                          *
 *                                                           *
 *  Bruno Blanchet, Vincent Cheval, and Marc Sylvestre       *
 *                                                           *
 *  Copyright (C) INRIA, CNRS 2000-2021                      *
 *                                                           *
 *************************************************************)

(*

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details (in file LICENSE).

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*)
(* String helper functions *)

(* [starts_with s sub] is true when the string [s] starts with
   [sub]. *)
val starts_with : string -> string -> bool

(* [ends_with s sub] is true when the string [s] ends with
   [sub]. *)
val ends_with : string -> string -> bool

(* [contains s sub] is true when [s] contains [sub] *)
val contains : string -> string -> bool

(* [pos s sub] returns [Some n'] when [s] contains [sub] at 
   position [n'], and [None] when [s] does not contain [sub]. *)
val pos : string -> string -> int option

(* [case_insensitive_ends_with s sub] is true when the string [s] ends with
   [sub]. Comparison is case insensitive. *)
val case_insensitive_ends_with : string -> string -> bool

(* [case_insensitive_contains s sub] is true when [s] contains [sub]. 
   Comparison is case insensitive. *)
val case_insensitive_contains : string -> string -> bool
