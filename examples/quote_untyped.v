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
  (* quote_untyped_term foo poseX. *)

  (* (* Ind *) *)
  (* quote_untyped_term nat poseX. *)

  (* (* Constr *) *)
  (* quote_untyped_term @nil poseX. *)
  (* quote_untyped_term @cons poseX. *)
  (* (* App *) *)
  (* quote_untyped_term (foo nat) poseX. *)
  (* (* quote_untyped_term (foo nat 1 2) poseX. *) *)
  (* (* quote_untyped_term (foo nat (bool nat) 2) poseX. *) *)

  (* (* Lambda *) *)
  (* quote_untyped_term (fun x : nat => x) poseX. *)

  (* (* App with w.e. *) *)
  (* quote_untyped_term ((fun x : bool => x) 1) poseX. *)

  (* (* Sorts *) *)
  (* quote_untyped_term Set poseX. *)
  (* quote_untyped_term Prop poseX. *)
  (* quote_untyped_term SProp poseX. *)
  (* quote_untyped_term Type poseX. *)


  (* (* Prod *) *)
  (* quote_untyped_term (forall x : nat, x) poseX. *)

  (* (* Let *) *)
  (* quote_untyped_term (let x : nat := true in foo) poseX. *)
  (* quote_untyped_term (let x : nat := true in x) poseX. *)
  (* try quote_untyped_term (let x := true in foo) poseX. *)

  (* (* Fix *) *)

  (* quote_untyped_term ((fix F ( x : bool ) : bool := x)) poseX. *)
  (* quote_term ((fix F ( x : bool ) : bool := x)) poseX. *)
  (* quote_untyped_term ((fix F ( x : bool ) (y := 2) : bool := x)) poseX. *)
  (* quote_term ((fix F ( x : bool ) (y := 2) : bool := x)) poseX. *)
  (* try quote_term ((fix F : bool := true)) poseX. *)
  (* quote_untyped_term ((fix F ( x : bool ) := F x)) poseX. *)
  (* quote_untyped_term (fix F ( x : bool ) : bool := G x with G ( n : nat) : nat := F x for F) poseX. *)
  (* quote_untyped_term (fix F ( x : bool ) : bool := G x with G ( n : nat) : nat := F x for G) poseX. *)

  (* Cases *)
  quote_untyped_term
    (match true as z in bool with | _ => 1 end) poseX.

  quote_term
    (match true as z in bool with | _ => 1 end) poseX.
  clear.
  (* Basic case, no return type *)
  quote_untyped_term
    (match true as z in bool with | true => true | false => false end) poseX.

  clear.
  (* Basic case, no ind information *)
  quote_untyped_term
    (match true as z with | true => true | false => false end) poseX.

  quote_term
    (match true as z with | true => true | false => false end) poseX.

  clear.

  quote_untyped_term
    (match true as z in bool, nil as y in (list _) with | true, nil => 0 | false, cons hd tl => hd | _, _ => 1 end) poseX.

  quote_term
    (match true as z in bool, nil as y in (list _) with | true, nil => 0 | false, cons hd tl => hd | _, _ => 1 end) poseX.
  clear.

  (* Basic case, no parameters *)
  quote_untyped_term
    (match true as z in bool return bool with | true => true | false => false end) poseX.
  quote_term
    (match true as z in bool return bool with | true => true | false => false end) poseX.
  clear.
  (* Ind with param + constructor with explicit and implicit arg *)
  quote_untyped_term
    (match @nil nat as z in list _ return bool with | nil => true | cons a _ => false end) poseX.
  quote_term
    (match @nil nat as z in list _ return bool with | nil => true | cons a _ => false end) poseX.
  clear.
  (* Ind with param + constructor with explicit args *)
  quote_untyped_term
    (match @nil nat as z in list _ return bool with | nil => true | cons hd tl => false end) poseX.
  quote_term
    (match @nil nat as z in list _ return bool with | nil => true | cons hd tl => false end) poseX.
  clear.
  (* Ind with param + constructor with explicit args + pat binder (nil) *)
  quote_untyped_term
    (match @nil nat as z in list _ return bool with | nil as x => true | cons hd tl => false end) poseX.
  (* Why not adding x? *)
  quote_term
    (match @nil nat as z in list _ return bool with | nil as x => true | cons hd tl => false end) poseX.
  clear.
  (* Ind with param + constructor with explicit args + pat binder (cons) *)
  quote_untyped_term
    (match @nil nat as z in list _ return bool with | nil => true | (cons hd tl) as x => false end) poseX.
  quote_term
    (match @nil nat as z in list _ return bool with | nil => true | (cons hd tl) as x => false end) poseX.
  clear.
  (* Ind with param + constructor with explicit args + pat binder (cons) and body references binder *)
  quote_untyped_term
    (match @nil nat as z in list _ return list nat with | nil => nil | (cons hd tl) as x => x end) poseX.
  (* quote replaces the body *)
  quote_term
    (match @nil nat as z in list _ return list nat with | nil => nil | (cons hd tl) as x => x end) poseX.
  clear.
  (* Ind with param + constructor with explicit args + pat binder in arg and body references orig binder *)
  quote_untyped_term
    (match @nil bool as z in list _ return bool with | nil => true | cons (hd as x) tl => hd end) poseX.
  (* Now quote uses rel *)
  quote_term
    (match @nil bool as z in list _ return bool with | nil => true | cons (hd as x) tl => hd end) poseX.
  (* Ind with param + constructor with explicit args + pat binder in arg and body references new binder *)
  quote_untyped_term
    (match @nil bool as z in list _ return bool with | nil => true | cons (hd as x) tl => x end) poseX.
  quote_term
    (match @nil bool as z in list _ return bool with | nil => true | cons (hd as x) tl => x end) poseX.

  clear.
  quote_untyped_term (match @nil bool as z in list _ return bool with | nil => true | cons (hd as x) (tl as y) => hd end) poseX.
  quote_term (match @nil bool as z in list _ return bool with | nil => true | cons (hd as x) (tl as y) => hd end) poseX.

  (* quote_term (match (cons 1 nil) as z in list _ return bool with | nil => true | cons _ _ => false end) poseX. *)

  quote_untyped_term (match (cons true nil) as z in list _ return bool with | nil => true | cons hd _ => hd end) poseX.
  quote_term (match (cons true nil) as z in list _ return bool with | nil => true | cons hd _ => hd end) poseX.
  clear.
  quote_untyped_term (match (cons (cons true nil) nil) as z in list _ return bool with
              | nil => true
              | cons (cons _ _) _ => false
              | _ => false end) poseX.
  quote_term (match (cons (cons true nil) nil) as z in list _ return bool with
              | nil => true
              | cons (cons _ _) _ => false
              | _ => false end) poseX.
  clear .

  quote_untyped_term (match (cons (cons true nil) nil) as z in list _ return bool with
              | nil => true
              | cons (cons hd tl) tl' => false
              | _ => false end) poseX.
  quote_term (match (cons (cons true nil) nil) as z in list _ return bool with
              | nil => true
              | cons (cons hd tl) tl' => false
              | _ => false end) poseX.
  quote_term (match (cons true nil) as z in list _ return bool with | nil => true | cons (hd as x) _ => hd end) poseX.
  quote_term (match (cons true nil) as z in list _ return bool with | nil => true | @cons _ hd _ => hd end) poseX.
  clear.
  quote_untyped_term
    (match true, false as z in bool return bool with
     | _, _ => true
     (* | true, false => true *)
     (* | false, true => true *)
     (* | false, false => true *)
    end) poseX.
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
