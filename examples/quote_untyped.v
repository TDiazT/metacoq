From MetaCoq.Template Require Import All.
(* From Coq Require Import Strings.String. *)
 (* Require Import String. *)

(* Notation "'Def' x" := (ltac:(run_template_program (tmPrint x) (fun y => idtac))) (at level 10). *)

(* Eval cbn in Def 2. *)
(* Compute Def 4. *)

Axiom (foo : nat).
Goal True.
Proof.
  quote_term 1 (fun y => pose y).
  quote_untyped_term x (fun x => pose x).

  quote_untyped_term foo (fun x => pose x).
  quote_untyped_term nat (fun x => pose x).
  quote_untyped_term (foo nat) (fun x => pose x).
  (* quote_untyped_term (foo nat 1 2) (fun x => pose x). *)
  (* quote_untyped_term (foo nat (bool nat) 2) (fun x => pose x). *)

  quote_term (fun x : nat => x) (fun x => pose x).
  quote_untyped_term (fun x : nat => x) (fun x => pose x).
  quote_untyped_term ((fun x : nat => x) 1) (fun x => pose x).
  quote_untyped_term ((fun x : bool => x) 1) (fun x => pose x).
  quote_untyped_term (forall x : nat, x) (fun x => pose x).


  quote_untyped_term nil (fun x => pose x).
  quote_untyped_term cons (fun x => pose x).
