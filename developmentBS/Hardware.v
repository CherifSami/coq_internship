(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2016)                 *)
(*                                                                             *)
(*  This software is a computer program whose purpose is to run a minimal,     *)
(*  hypervisor relying on proven properties such as memory isolation.          *)
(*                                                                             *)
(*  This software is governed by the CeCILL license under French law and       *)
(*  abiding by the rules of distribution of free software.  You can  use,      *)
(*  modify and/ or redistribute the software under the terms of the CeCILL     *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL          *)
(*  "http://www.cecill.info".                                                  *)
(*                                                                             *)
(*  As a counterpart to the access to the source code and  rights to copy,     *)
(*  modify and redistribute granted by the license, users are provided only    *)
(*  with a limited warranty  and the software's author,  the holder of the     *)
(*  economic rights,  and the successive licensors  have only  limited         *)
(*  liability.                                                                 *)
(*                                                                             *)
(*  In this respect, the user's attention is drawn to the risks associated     *)
(*  with loading,  using,  modifying and/or developing or reproducing the      *)
(*  software by the user in light of its specific status of free software,     *)
(*  that may mean  that it is complicated to manipulate,  and  that  also      *)
(*  therefore means  that it is reserved for developers  and  experienced      *)
(*  professionals having in-depth computer knowledge. Users are therefore      *)
(*  encouraged to load and test the software's suitability as regards their    *)
(*  requirements in conditions enabling the security of their systems and/or   *)
(*  data to be ensured and,  more generally, to use and operate it in the      *)
(*  same conditions as regards security.                                       *)
(*                                                                             *)
(*  The fact that you are presently reading this means that you have had       *)
(*  knowledge of the CeCILL license and that you accept its terms.             *)
(*******************************************************************************)

(** * Summary 
    This file contains the monad state and Hoare logic formalization.
     + State monad formalization : 
        ** The type constructor "LLI"
        ** Two operations : "bind" to compose a sequence of monadic functions 
           and "ret" to create monadic values. 
     + We use state monad to simulate side effects like state updates so we 
       define the following functions: 
        ** "get" to get back the current state
        ** "put" to update the current state  
     + The state contains mainly the physical memory.
       In our Hardware model, physical memory is an associaton list that keeps 
       only relevent data. Its key is a the physical address and the value is 
       the data to store into physical memory.
     + Hoare logic formalization : "{{ P }} m {{ Q }}"
        ** "m" is a monadic function 
        ** "P" is the precondition of the function "m", it is an unary predicate 
            which depends on the state
        ** "Q" is the postcondition of the function "m", it is a binary predicate
            which depends on the new state and the return value
       We define some lemmas like "weaken" and "bindWP" to facilitate Hoare logic 
       and monad manipulation.
*)
Require Import ADT.

Record Pentry : Type:=
{read :bool;
 write : bool ;
 exec : bool;
 present : bool;
 user    : bool;
 pa      : page
}.

Record Ventry : Type:=
{
 pd : bool;
 va : vaddr
}.

Inductive value : Type:= 
|PE : Pentry -> value
|VE : Ventry -> value
|PP : page -> value
|VA : vaddr -> value
|I  : index -> value.  


Record state : Type := {
 currentPartition : page;
 memory : list (paddr * value)
}.
