From MetaCoq.Template Require Import All.
(* From Coq Require Import Strings.String. *)
 (* Require Import String. *)

(* Notation "'Def' x" := (ltac:(run_template_program (tmPrint x) (fun y => idtac))) (at level 10). *)

(* Eval cbn in Def 2. *)
(* Compute Def 4. *)



Ltac poseX := fun x => pose x.
Axiom (foo : nat).
Goal True.
Proof.
  (* Var *)
  quote_untyped_term foo poseX.

  (* Ind *)
  quote_untyped_term nat poseX.

  (* Constr *)
  quote_untyped_term @nil poseX.
  quote_untyped_term @cons poseX.
  (* App *)
  quote_untyped_term (foo nat) poseX.
  (* quote_untyped_term (foo nat 1 2) poseX. *)
  (* quote_untyped_term (foo nat (bool nat) 2) poseX. *)

  (* Lambda *)
  quote_untyped_term (fun x : nat => x) poseX.

  (* App with w.e. *)
  quote_untyped_term ((fun x : bool => x) 1) poseX.

  (* Sorts *)
  quote_untyped_term Set poseX.
  quote_untyped_term Prop poseX.
  quote_untyped_term SProp poseX.
  quote_untyped_term Type poseX.


  (* Prod *)
  quote_untyped_term (forall x : nat, x) poseX.

  (* Let *)
  quote_untyped_term (let x : nat := true in foo) poseX.
  quote_untyped_term (let x : nat := true in x) poseX.
  try quote_untyped_term (let x := true in foo) poseX.

  (* Fix *)

  quote_untyped_term ((fix F ( x : bool ) : bool := F x)) poseX.
  quote_untyped_term (fix F ( x : bool ) : bool := G x with G ( n : nat) : nat := F x for F) poseX.
  quote_untyped_term (fix F ( x : bool ) : bool := G x with G ( n : nat) : nat := F x for G) poseX.

Abort.

Fixpoint to_rel (ctx : context) (t : term) : term :=
  match t with
  | tVar x => l


Section test.
    Variables n foobar : nat.

    Goal True.
    (* quote_untyped_term nat poseX. *)
    quote_untyped_term n poseX.
    quote_untyped_term foobar poseX.
    Definition test1 := $quote_untyped nat.
    Definition test := $quote_untyped n.
