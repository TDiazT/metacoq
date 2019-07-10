(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template Require Import config monad_utils utils BasicAst AstUtils UnivSubst uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity PCUICWeakening PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSafeReduce PCUICSafeConversion.

Import MonadNotation.
Open Scope type_scope.
Open Scope list_scope.

(* from Validity.v *)

(* todo: move this *)
Arguments All_nil {_ _}.
Arguments All_cons {_ _ _ _}.

Axiom todo : forall {A}, A.


Lemma All_sq {A} {P : A -> Type} {l}
  : All (fun x => ∥ P x ∥) l -> ∥ All P l ∥.
Proof.
  induction 1.
  - repeat constructor.
  - sq; now constructor.
Qed.

Lemma All2_sq {A B} {R : A -> B -> Type} {l1 l2}
  : All2 (fun x y => ∥ R x y ∥) l1 l2 -> ∥ All2 R l1 l2 ∥.
Proof.
  induction 1.
  - repeat constructor.
  - sq; now constructor.
Qed.


Lemma weakening_sq `{cf : checker_flags} {Σ Γ} Γ' {t T} :
  ∥ wf Σ.1 ∥ -> ∥ wf_local Σ (Γ ,,, Γ') ∥ ->
  ∥ Σ ;;; Γ |- t : T ∥ ->
  ∥ Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T ∥.
Proof.
  intros; sq; now eapply weakening.
Defined.

Definition wf_local_rel_abs_sq `{cf : checker_flags} {Σ Γ Γ' A na} :
  ∥ wf_local_rel Σ Γ Γ' ∥ -> {u & ∥ Σ ;;; Γ ,,, Γ' |- A : tSort u ∥ }
  -> ∥ wf_local_rel Σ Γ (Γ',, vass na A) ∥.
Proof.
  intros H [u Hu]; sq. now eapply wf_local_rel_abs.
Qed.

Definition wf_local_rel_def_sq `{cf : checker_flags} {Σ Γ Γ' t A na} :
  ∥ wf_local_rel Σ Γ Γ' ∥ -> ∥ isType Σ (Γ ,,, Γ') A ∥ -> ∥ Σ ;;; Γ ,,, Γ' |- t : A ∥
  -> ∥ wf_local_rel Σ Γ (Γ',, vdef na t A) ∥.
Proof.
  intros; sq. now eapply wf_local_rel_def.
Qed.

Definition wf_local_rel_app_inv_sq `{cf : checker_flags} {Σ Γ1 Γ2 Γ3} :
  ∥ wf_local_rel Σ Γ1 Γ2 ∥ -> ∥ wf_local_rel Σ (Γ1 ,,, Γ2) Γ3 ∥
  -> ∥ wf_local_rel Σ Γ1 (Γ2 ,,, Γ3) ∥.
Proof.
  intros; sq; now eapply wf_local_rel_app_inv.
Qed.

Fixpoint monad_All {T} {M : Monad T} {A} {P} (f : forall x, T (P x)) l : T (@All A P l)
  := match l with
     | [] => ret All_nil
     | a :: l => X <- f a ;;
                Y <- monad_All f l ;;
                ret (All_cons X Y)
     end.

Fixpoint monad_All2 {T E} {M : Monad T} {M' : MonadExc E T} wrong_sizes
         {A B R} (f : forall x y, T (R x y)) l1 l2
  : T (@All2 A B R l1 l2)
  := match l1, l2 with
     | [], [] => ret (All2_nil R)
     | a :: l1, b :: l2 => X <- f a b ;;
                          Y <- monad_All2 wrong_sizes f l1 l2 ;;
                          ret (All2_cons R a b l1 l2 X Y)
     | _, _ => raise wrong_sizes
     end.


Definition monad_prod {T} {M : Monad T} {A B} (x : T A) (y : T B): T (A * B)
  := X <- x ;; Y <- y ;; ret (X, Y).

Definition check_dec {T E} {M : Monad T} {M' : MonadExc E T} (e : E) {P}
           (H : {P} + {~ P})
  : T P
  := match H with
     | left x => ret x
     | right _ => raise e
     end.

Definition check_eq_true {T E} {M : Monad T} {M' : MonadExc E T} b (e : E)
  : T (b = true)
  := if b return T (b = true) then ret eq_refl else raise e.


Definition mkApps_decompose_app_rec t l :
  mkApps t l = mkApps  (fst (decompose_app_rec t l)) (snd (decompose_app_rec t l)).
Proof.
  revert l; induction t; try reflexivity.
  intro l; cbn in *.
  transitivity (mkApps t1 ((t2 ::l))). reflexivity.
  now rewrite IHt1.
Qed.

Definition mkApps_decompose_app t :
  t = mkApps  (fst (decompose_app t)) (snd (decompose_app t))
  := mkApps_decompose_app_rec t [].


Derive EqDec for sort_family.
Next Obligation.
  unfold Classes.dec_eq. decide equality.
Defined.


Inductive type_error :=
| UnboundRel (n : nat)
| UnboundVar (id : string)
| UnboundEvar (ev : nat)
| UndeclaredConstant (c : string)
| UndeclaredInductive (c : inductive)
| UndeclaredConstructor (c : inductive) (i : nat)
| NotConvertible (Γ : context) (t u t' u' : term)
| NotASort (t : term)
| NotAProduct (t t' : term)
| NotAnInductive (t : term)
| IllFormedFix (m : mfixpoint term) (i : nat)
| UnsatisfiedConstraints (c : ConstraintSet.t)
| Msg (s : string).

Definition NotConvertible' Γ t u := NotConvertible Γ t u t u.

Lemma lookup_env_id Σ id decl
  : lookup_env Σ id = Some decl -> id = global_decl_ident decl.
Proof.
  induction Σ; cbn. inversion 1.
  destruct (ident_eq_spec id (global_decl_ident a)).
  - inversion 1. now destruct H1.
  - easy.
Qed.



Local Open Scope string_scope.
Definition string_of_list_aux {A} (f : A -> string) (l : list A) : string :=
  let fix aux l :=
      match l return string with
      | nil => ""
      | cons a nil => f a
      | cons a l => f a ++ "," ++ aux l
      end
  in aux l.

Definition string_of_list {A} (f : A -> string) (l : list A) : string :=
  "[" ++ string_of_list_aux f l ++ "]".

Definition string_of_level (l : Level.t) : string :=
  match l with
  | Level.lProp => "Prop"
  | Level.lSet => "Set"
  | Level.Level s => s
  | Level.Var n => "Var" ++ string_of_nat n
  end.

Definition string_of_level_expr (l : Level.t * bool) : string :=
  let '(l, b) := l in
  string_of_level l ++ (if b then "+1" else "").

Definition string_of_sort (u : universe) :=
  string_of_list string_of_level_expr u.
Definition string_of_name (na : name) :=
  match na with
  | nAnon => "Anonymous"
  | nNamed n => n
  end.
Definition string_of_universe_instance u :=
  string_of_list string_of_level u.

Definition string_of_def {A : Set} (f : A -> string) (def : def A) :=
  "(" ++ string_of_name (dname def) ++ "," ++ f (dtype def) ++ "," ++ f (dbody def) ++ ","
      ++ string_of_nat (rarg def) ++ ")".

Definition string_of_inductive (i : inductive) :=
  (inductive_mind i) ++ "," ++ string_of_nat (inductive_ind i).

Fixpoint string_of_term (t : term) :=
  match t with
  | tRel n => "Rel(" ++ string_of_nat n ++ ")"
  | tVar n => "Var(" ++ n ++ ")"
  | tEvar ev args => "Evar(" ++ string_of_nat ev ++ "[]" (* TODO *)  ++ ")"
  | tSort s => "Sort(" ++ string_of_sort s ++ ")"
  | tProd na b t => "Prod(" ++ string_of_name na ++ "," ++
                            string_of_term b ++ "," ++ string_of_term t ++ ")"
  | tLambda na b t => "Lambda(" ++ string_of_name na ++ "," ++ string_of_term b
                                ++ "," ++ string_of_term t ++ ")"
  | tLetIn na b t' t => "LetIn(" ++ string_of_name na ++ "," ++ string_of_term b
                                 ++ "," ++ string_of_term t' ++ "," ++ string_of_term t ++ ")"
  | tApp f l => "App(" ++ string_of_term f ++ "," ++ string_of_term l ++ ")"
  | tConst c u => "Const(" ++ c ++ "," ++ string_of_universe_instance u ++ ")"
  | tInd i u => "Ind(" ++ string_of_inductive i ++ "," ++ string_of_universe_instance u ++ ")"
  | tConstruct i n u => "Construct(" ++ string_of_inductive i ++ "," ++ string_of_nat n ++ ","
                                    ++ string_of_universe_instance u ++ ")"
  | tCase (ind, i) t p brs =>
    "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
            ++ string_of_term p ++ "," ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
  | tProj (ind, i, k) c =>
    "Proj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
            ++ string_of_term c ++ ")"
  | tFix l n => "Fix(" ++ (string_of_list (string_of_def string_of_term) l) ++ "," ++ string_of_nat n ++ ")"
  | tCoFix l n => "CoFix(" ++ (string_of_list (string_of_def string_of_term) l) ++ "," ++ string_of_nat n ++ ")"
  end.

Definition string_of_type_error (e : type_error) : string :=
  match e with
  | UnboundRel n => "Unboound rel " ++ string_of_nat n
  | UnboundVar id => "Unbound var " ++ id
  | UnboundEvar ev => "Unbound evar " ++ string_of_nat ev
  | UndeclaredConstant c => "Undeclared constant " ++ c
  | UndeclaredInductive c => "Undeclared inductive " ++ (inductive_mind c)
  | UndeclaredConstructor c i => "Undeclared inductive " ++ (inductive_mind c)
  | NotConvertible Γ t u t' u' => "Terms are not convertible: " ++
      string_of_term t ++ " " ++ string_of_term u ++ " after reduction: " ++
      string_of_term t' ++ " " ++ string_of_term u'
  | NotASort t => "Not a sort"
  | NotAProduct t t' => "Not a product"
  | NotAnInductive t => "Not an inductive"
  | IllFormedFix m i => "Ill-formed recursive definition"
  | UnsatisfiedConstraints c => "Unsatisfied constraints"
  | Msg s => "Msg" ++ s
  end.

Inductive typing_result (A : Type) :=
| Checked (a : A)
| TypeError (t : type_error).
Global Arguments Checked {A} a.
Global Arguments TypeError {A} t.

Instance typing_monad : Monad typing_result :=
  {| ret A a := Checked a ;
     bind A B m f :=
       match m with
       | Checked a => f a
       | TypeError t => TypeError t
       end
  |}.

Instance monad_exc : MonadExc type_error typing_result :=
  { raise A e := TypeError e;
    catch A m f :=
      match m with
      | Checked a => m
      | TypeError t => f t
      end
  }.


Definition iscumul `{cf : checker_flags} Σ HΣ Γ := isconv_term RedFlags.default Σ HΣ Γ Cumul.


Definition strengthening `{cf : checker_flags} {Σ Γ Γ' Γ'' t T}
  : wf Σ.1 -> Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |-
               lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T ->
    Σ;;; Γ ,,, Γ' |- t : T.
Admitted.


Lemma wf_local_rel_inv `{checker_flags} {Σ Γ1 Γ2} (w : wf_local_rel Σ Γ1 Γ2) :
  forall d Γ2', Γ2 = Γ2' ,, d ->
  wf_local_rel Σ Γ1 Γ2' × (∑ u, Σ ;;; Γ1 ,,, Γ2' |- d.(decl_type) : tSort u) ×
               match d.(decl_body) with
               | Some b => Σ ;;; Γ1 ,,, Γ2' |- b : d.(decl_type)
               | None => True
               end.
Proof.
  intros d Γ.
  destruct w; inversion 1; subst; cbn in *.
  split; [assumption|]. split; [assumption| trivial].
  split; [assumption|]. split; [assumption| trivial].
Defined.

Definition strengthening_wf_local_rel `{cf : checker_flags} Σ Γ1 Γ2 Γ3 Γ4 :
  wf Σ.1 -> wf_local_rel Σ Γ1 (Γ2 ,,, Γ3 ,,, lift_context #|Γ3| 0 Γ4)
  -> wf_local_rel Σ Γ1 (Γ2 ,,, Γ4).
Proof.
  intros HΣ H.
  eapply wf_local_rel_app in H; destruct H as [H1 H2].
  eapply wf_local_rel_app in H1; destruct H1 as [H1 H1'].
  eapply wf_local_rel_app_inv. assumption.
  revert H2. clear -HΣ. induction Γ4. intros; constructor.
  intro H. rewrite lift_context_snoc0 in H.
  destruct a as [na [b|] ty].
  - unfold lift_decl, map_decl in H; cbn in H.
    destruct (wf_local_rel_inv H _ _ eq_refl) as [H1 [H2 H3]]; cbn in *.
    rewrite Nat.add_0_r in *.
    rewrite app_context_assoc in *.
    econstructor.
    + easy.
    + cbn. exists H2.π1. eapply strengthening. assumption. exact H2.π2.
    + cbn. eapply strengthening; eassumption.
  - unfold lift_decl, map_decl in H; cbn in H.
    destruct (wf_local_rel_inv H _ _ eq_refl) as [H1 [[u H2] _]]; cbn in *.
    rewrite Nat.add_0_r in H2.
    rewrite app_context_assoc in H2.
    econstructor. easy.
    exists u. eapply strengthening; eassumption.
Qed.


Definition wf_local_app_inv `{cf : checker_flags} {Σ Γ1 Γ2} :
  wf_local Σ Γ1 -> wf_local_rel Σ Γ1 Γ2
  -> wf_local Σ (Γ1 ,,, Γ2).
Proof.
  intros H1 H2.
  apply wf_local_local_rel, wf_local_rel_app_inv.
  now apply wf_local_rel_local.
  now rewrite app_context_nil_l.
Defined.

Lemma map_option_out_mapi {A B} (l : list A) (l' : list B) f P
  : map_option_out (mapi f l) = Some l'
    -> Alli (fun i x => on_Some_or_None P (f i x)) 0 l
    -> All P l'.
Proof.
  unfold mapi. generalize 0.
  induction l in l' |- *; simpl; intro n.
  - inversion 1; constructor.
  - case_eq (f n a); [|discriminate].
    intros b Hb. 
    case_eq (map_option_out (mapi_rec f l (S n))); [|discriminate].
    intros l0 Hl0 HH0 HH1.
    inversion HH0; subst; clear HH0.
    inversion HH1; subst.
    constructor. now rewrite Hb in H0.
    now eapply IHl.
Qed.

Lemma Alli_id {A} {P : nat -> A -> Type} (l : list A) (n : nat)
  : (forall n x, P n x) -> Alli P n l.
Proof.
  intro H; induction l in n |- *; constructor; eauto.
Qed.


Lemma type_Case_csqce {cf:checker_flags} Σ Γ ind u p args mdecl idecl
      (isdecl : declared_inductive (fst Σ) mdecl ind idecl)
      (pars := List.firstn mdecl.(ind_npars) args)
      pty (Hp : Σ ;;; Γ |- p : pty)
      indctx pctx ps btys
      (e : types_of_case ind mdecl idecl pars u p pty = Some (indctx, pctx, ps, btys))
      (Hc : PCUICTyping.check_correct_arity (global_ext_constraints Σ) idecl ind u indctx pars pctx)
  : Forall (fun A : nat × term => wellformed Σ Γ (snd A)) btys.
Proof.
  unfold types_of_case in e.
    case_eq (instantiate_params (ind_params mdecl) pars (ind_type idecl));
      [|intro HH; rewrite HH in e; discriminate e].
    intros params' He; rewrite He in e.
    case_eq (destArity [] params');
      [|intro HH; rewrite HH in e; discriminate e].
    intros [params_ctx params_sort] He1; rewrite He1 in e.
    case_eq (destArity [] pty);
      [|intro HH; rewrite HH in e; discriminate e].
    intros [pty_ctx pty_sort] He2; rewrite He2 in e.

    case_eq (map_option_out (build_branches_type ind mdecl idecl pars u p));
      [|intro HH; rewrite HH in e; discriminate e].
    intros brtys He3; rewrite He3 in e.
    inversion e; subst; clear e.
    unfold build_branches_type in He3.
    solve_all.
    eapply (map_option_out_mapi (ind_ctors idecl) btys _ _ He3); clear He3. 
    apply Alli_id.
    intros i [[id ctor] k].
    case_eq (instantiate_params (ind_params mdecl) pars ((subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))) (subst_instance_constr u ctor))); [|cbn; trivial].
    intros ipars Hipars.
    case_eq (decompose_prod_assum [] ipars). intros ipars0 ipars1 ipars01.
    case_eq (chop (ind_npars mdecl) (snd (decompose_app ipars1))).
    intros ipars10 ipars11 Hipars1. cbn.
    (* left. econstructor. *)
    (* clear params' He. *)

    (* apply PCUICWeakeningEnv.on_declared_inductive in X2; try assumption. *)
    (* destruct X2 as [XX2 XX3]. *)
    (* apply onConstructors in XX3; unfold on_constructors in XX3. *)
    (* eapply Alli_impl; try eassumption. *)
    (* clear -He. *)
    (* intros n [[id ctor_ty] nc] X. *)
    (* destruct X as [X1 X2]; cbn in *. *)
Admitted.




Definition fix_context_i i mfix :=
  List.rev (mapi_rec (fun i (d : BasicAst.def term)
                      => vass (dname d) ((lift0 i) (dtype d))) mfix i).

Lemma lift_fix_context mfix : forall k k' j, j <= k ->
    fix_context_i (k + k') mfix = lift_context k' j (fix_context_i k mfix).
Proof.
  induction mfix. reflexivity.
  intros k k' j Hj.
  change ([vass (dname a) ((lift0 (k + k')) (dtype a))] ,,, fix_context_i (S (k + k')) mfix = lift_context k' j ([vass (dname a) ((lift0 k) (dtype a))] ,,, fix_context_i (S k) mfix)).
  erewrite lift_context_app, (IHmfix (S k) k' (S j)); cbn.
  unfold map_decl, vass; cbn. now rewrite simpl_lift.
  now apply le_n_S.
Qed.



Section Typecheck.
  Context `{cf : checker_flags} {Σ : global_env_ext} {HΣ : ∥ wf Σ ∥}.
  Let G := match gc_of_constraints (global_ext_constraints Σ) with
           | Some ctrs => make_graph ctrs
           | None => todo
           end.

  Definition cumul_red_l' (Γ : context) (t u : term)
    : red (fst Σ) Γ t u -> Σ;;; Γ |- t <= u.
  Proof.
    induction 1. eapply cumul_refl'.
    eapply cumul_trans. eassumption.
    eapply cumul_red_l. eassumption.
    eapply cumul_refl'.
  Defined.

  Lemma type_reduction {Γ t A B}
    : wf Σ -> wf_local Σ Γ -> Σ ;;; Γ |- t : A -> red (fst Σ) Γ A B -> Σ ;;; Γ |- t : B.
  Proof.
    intros HΣ' HΓ Ht Hr.
    econstructor. eassumption.
    2: now eapply cumul_red_l'.
    destruct (validity_term HΣ' HΓ Ht).
    - left. eapply isWfArity_red; try eassumption.
      apply RedFlags.default.
    - destruct i as [s HA]. right.
      exists s. eapply subject_reduction; eassumption.
  Defined.

  Definition isType_wellformed {Γ t}
    : isType Σ Γ t -> wellformed Σ Γ t.
  Proof.
    intros []. left; now econstructor.
  Qed.

  (* Definition typ_to_wf {Γ t} *)
  (*   : { A : term | ∥ Σ ;;; Γ |- t : A ∥ } -> wellformed Σ Γ t. *)
  (* Proof. *)
  (*   intros [A h]. sq. left. now exists A. *)
  (* Defined. *)

  Lemma validity_wf {Γ t T} :
    ∥ wf_local Σ Γ ∥ -> ∥ Σ ;;; Γ |- t : T ∥ -> wellformed Σ Γ T.
  Proof.
    destruct HΣ as [wΣ]. intros [wΓ] [X].
    intros. eapply validity_term in X; try assumption.
    destruct X. now right.
    left; destruct i. now exists (tSort x).
  Defined.

  Definition hnf := reduce_term RedFlags.default Σ HΣ.

  Theorem hnf_sound {Γ t h} : ∥ red (fst Σ) Γ t (hnf Γ t h) ∥.
  Proof.
    apply reduce_term_sound.
  Defined.

  Program Definition reduce_to_sort Γ t (h : wellformed Σ Γ t)
    : typing_result (∑ u, ∥ red (fst Σ) Γ t (tSort u) ∥) :=
    match t with
    | tSort s => ret (s; sq (refl_red _ _ _))
    | _ =>
      match hnf Γ t h with
      | tSort s => ret (s; _)
      | _ => raise (NotASort t)
      end
    end.
  Next Obligation.
    pose proof (hnf_sound (h:=h)).
    now rewrite <- Heq_anonymous in H0.
  Defined.

  Program Definition reduce_to_prod Γ t (h : wellformed Σ Γ t)
       : typing_result (∑ na a b, ∥ red (fst Σ) Γ t (tProd na a b) ∥) :=
    match t with
    | tProd na a b => ret (na; a; b; sq (refl_red _ _ _))
    | _ =>
      match hnf Γ t h with
      | tProd na a b => ret (na; a; b; _)
      | t' => raise (NotAProduct t t')
      end
    end.
  Next Obligation.
    pose proof (hnf_sound (h:=h)).
    now rewrite <- Heq_anonymous in H0.
  Defined.

  Fixpoint stack_to_apps π : typing_result (list term) :=
    match π with
    | Empty => ret []
    | App t π => l <- stack_to_apps π ;; ret (t :: l)
    | _ => raise (Msg "not some applications")
    end.

  Lemma zip_stack_to_apps t π l :
    stack_to_apps π = Checked l -> zipc t π = mkApps t l.
  Proof.
    revert t l. induction π; cbn; try inversion 1.
    reflexivity.
    destruct (stack_to_apps π); inversion H1.
    erewrite IHπ; reflexivity.
  Qed.


  Program Definition reduce_to_ind Γ t (h : wellformed Σ Γ t)
    : typing_result (∑ i u l, ∥ red (fst Σ) Γ t (mkApps (tInd i u) l) ∥) :=
    match decompose_app t with
    | (tInd i u, l) => ret (i; u; l; sq _)
    | _ =>
      match reduce_stack RedFlags.default Σ HΣ Γ t Empty h with
      | (tInd i u, π) => match stack_to_apps π with
                        | Checked l => ret (i; u; l; _)
                        | TypeError e => raise e
                        end
      | _ => raise (NotAnInductive t)
      end
    end.
  Next Obligation.
    assert (X : mkApps (tInd i u) l = t); [|rewrite X; apply refl_red].
    etransitivity. 2: symmetry; eapply mkApps_decompose_app.
    pose proof (f_equal fst Heq_anonymous) as X; cbn in X; rewrite X; clear X.
    pose proof (f_equal snd Heq_anonymous) as X; cbn in X; rewrite X; clear X.
    reflexivity.
  Defined.
  Next Obligation.
    pose proof (reduce_stack_sound RedFlags.default Σ HΣ _ _ Empty h).
    rewrite <- Heq_anonymous1 in H0.
    now erewrite <- zip_stack_to_apps.
  Defined.

  Definition leqb_term := eqb_term_upto_univ (try_is_eq_universe G)
                                             (try_is_leq_universe G).

  Definition eqb_term := eqb_term_upto_univ (try_is_eq_universe G)
                                            (try_is_eq_universe G).


  Lemma try_is_leq_universe_spec u1 u2 :
    try_is_leq_universe G u1 u2 -> leq_universe (global_ext_constraints Σ) u1 u2.
  Admitted.

  Lemma try_is_eq_universe_spec u1 u2 :
    try_is_eq_universe G u1 u2 -> eq_universe (global_ext_constraints Σ) u1 u2.
  Admitted.

  Lemma eq_term_upto_univ_impl :
    forall (equ lequ : _ -> _ -> bool) Re Rle,
      (forall u u', equ u u' -> Re u u') ->
      (forall u u', lequ u u' -> Rle u u') ->
      forall t t', eqb_term_upto_univ equ lequ t t' -> eq_term_upto_univ Re Rle t t'.
  Proof.
  intros equ lequ Re Rle he hle t t'.
  induction t in t', lequ, Rle, hle |- * using term_forall_list_ind.
  all: destruct t'; try discriminate 1. all: cbn.
  - intro H; change (eqb n n0 = true) in H; destruct (eqb_spec n n0);
      [subst; constructor|discriminate].
  - intro H; change (eqb i i0 = true) in H; destruct (eqb_spec i i0);
      [subst; constructor|discriminate].
  - intro H. toProp.
    change (eqb n n0 = true) in H; destruct (eqb_spec n n0);
      [subst|discriminate].
    constructor.
  Admitted.

  Lemma leqb_term_spec t u :
    leqb_term t u -> leq_term (global_ext_constraints Σ) t u.
  Proof.
    apply eq_term_upto_univ_impl.
    apply try_is_eq_universe_spec.
    apply try_is_leq_universe_spec.
  Qed.

  Lemma eqb_term_spec t u :
    eqb_term t u -> eq_term (global_ext_constraints Σ) t u.
  Proof.
    apply eq_term_upto_univ_impl.
    all: apply try_is_eq_universe_spec.
  Qed.


  Program Definition convert_leq Γ t u
          (ht : wellformed Σ Γ t) (hu : wellformed Σ Γ u)
    : typing_result (∥ Σ ;;; Γ |- t <= u ∥) :=
    match leqb_term t u with true => ret _ | false =>
    match iscumul Σ HΣ Γ t ht u hu with
    | true => ret _
    | false => (* fallback *)  (* nico *)
      let t' := hnf Γ t ht in
      let u' := hnf Γ u hu in
      (* match leq_term (snd Σ) t' u' with true => ret _ | false => *)
      raise (NotConvertible Γ t u t' u')
      (* end *)
    end end.
  Next Obligation.
    symmetry in Heq_anonymous; apply leqb_term_spec in Heq_anonymous.
    constructor. now constructor.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous; apply isconv_term_sound in Heq_anonymous.
    assumption.
  Qed.

  (* nico *)
  Lemma isWfArity_or_Type_cumul : forall {Γ A A'},
      Σ;;; Γ |- A' <= A -> isWfArity_or_Type Σ Γ A' -> isWfArity_or_Type Σ Γ A.
  Admitted.

  Section InferAux.
    Variable (infer : forall Γ (HΓ : ∥ wf_local Σ Γ ∥) (t : term),
                 typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ })).

    Program Definition infer_type Γ HΓ t
      : typing_result ({u : universe & ∥ Σ ;;; Γ |- t : tSort u ∥}) :=
      tx <- infer Γ HΓ t ;;
      u <- reduce_to_sort Γ tx.π1 _ ;;
      ret (u.π1; _).
    Next Obligation.
      eapply validity_wf; eassumption.
    Defined.
    Next Obligation.
      destruct HΣ, HΓ, X, X0.
      now constructor; eapply type_reduction.
    Defined.

    Program Definition infer_cumul Γ HΓ t A (hA : wellformed Σ Γ A)
      : typing_result (∥ Σ ;;; Γ |- t : A ∥) :=
      A' <- infer Γ HΓ t ;;
      X <- convert_leq Γ A'.π1 A _ hA ;;  (* nico *)
      ret _.
    Next Obligation. now eapply validity_wf. Qed.
    Next Obligation.
      destruct hA as [[s hs]|].
      - destruct HΣ, HΓ, X, X0. constructor. econstructor; try eassumption. 
        apply validity_term in X0; try assumption.
        eapply isWfArity_or_Type_cumul; eassumption.
      - destruct HΣ, HΓ, X, X0, H. constructor. econstructor; easy.
    Qed.
  End InferAux.


  Program Definition lookup_ind_decl ind
    : typing_result
        ({decl & {body & declared_inductive (fst Σ) decl ind body}}) :=
    match lookup_env (fst Σ) ind.(inductive_mind) with
    | Some (InductiveDecl _ decl) =>
      match nth_error decl.(ind_bodies) ind.(inductive_ind) with
      | Some body => ret (decl; body; _)
      | None => raise (UndeclaredInductive ind)
      end
    | _ => raise (UndeclaredInductive ind)
    end.
  Next Obligation.
    split.
    - symmetry in Heq_anonymous0.
      etransitivity. eassumption.
      erewrite (lookup_env_id _ _ _ Heq_anonymous0); reflexivity.
    - now symmetry.
  Defined.

  Definition check_consistent_constraints cstrs u
    : typing_result (consistent_instance_ext Σ cstrs u).
  Admitted.
    (* match cstrs as cstrs' return (cstrs' = cstrs -> typing_result (consistent_universe_context_instance Σ cstrs' u)) with *)
    (* | Monomorphic_ctx ctx => fun _ => ret I *)
    (* | Polymorphic_ctx (t, c) *)
    (* | Cumulative_ctx ((t, c), _) => fun _ => *)
    (*     (if #|t| =? #|u| as b return (b = (#|t| =? #|u|) -> typing_result (#|t| = #|u| /\ check_constraints (snd Σ) (subst_instance_cstrs u c) = true)) *)
    (*      then fun Heqb => *)
    (*        (if check_constraints (snd Σ) (subst_instance_cstrs u c) as b *)
    (*            return (b = check_constraints (snd Σ) (subst_instance_cstrs u c) -> typing_result (#|t| = #|u| /\ b = true)) *)
    (*         then fun _ => ret (conj (beq_nat_eq #|t| #|u| Heqb) eq_refl) *)
    (*         else fun _ => raise (UnsatisfiedConstraints (subst_instance_cstrs u c))) *)
    (*          eq_refl *)
    (*      else *)
    (*        fun _ => raise (UnboundVar "wrong length of instance")) *)
    (*       eq_refl *)
    (* end eq_refl. *)



  Definition eqb_opt_term (t u : option term) :=
    match t, u with
    | Some t, Some u => eqb_term t u
    | None, None => true
    | _, _ => false
    end.


  Lemma eqb_opt_term_spec t u
    : eqb_opt_term t u -> eq_opt_term (global_ext_constraints Σ) t u.
  Proof.
    destruct t, u; try discriminate; cbn.
    apply eqb_term_spec. trivial.
  Qed.

  Definition eqb_decl (d d' : context_decl) :=
    eqb_opt_term d.(decl_body) d'.(decl_body) && eqb_term d.(decl_type) d'.(decl_type).

  Lemma eqb_decl_spec d d'
    : eqb_decl d d' -> eq_decl (global_ext_constraints Σ) d d'.
  Proof.
    unfold eqb_decl, eq_decl.
    intro H. toProp. apply eqb_opt_term_spec in H.
    apply eqb_term_spec in H0. now split.
  Qed.

  Definition eqb_context (Γ Δ : context) := forallb2 eqb_decl Γ Δ.

  Lemma eqb_context_spec Γ Δ
    : eqb_context Γ Δ -> eq_context (global_ext_constraints Σ) Γ Δ.
  Proof.
    unfold eqb_context, eq_context.
    intro HH. apply forallb2_All2 in HH.
    eapply All2_impl; try eassumption.
    cbn. apply eqb_decl_spec.
  Qed.

  Definition check_correct_arity decl ind u ctx pars pctx :=
    let inddecl :=
        {| decl_name := nNamed decl.(ind_name);
           decl_body := None;
           decl_type := mkApps (tInd ind u) (map (lift0 #|ctx|) pars ++ to_extended_list ctx) |}
    in eqb_context (inddecl :: ctx) pctx.

  Lemma check_correct_arity_spec decl ind u ctx pars pctx
    : check_correct_arity decl ind u ctx pars pctx
      -> PCUICTyping.check_correct_arity (global_ext_constraints Σ) decl ind u ctx pars pctx.
  Proof.
    apply eqb_context_spec.
  Qed.


  Ltac sq :=
    repeat match goal with
           | H : ∥ _ ∥ |- _ => case H; clear H; intro H
           end; try eapply sq.

  (* Definition sq_type_CoFix {Γ mfix n decl} : *)
  (*   allow_cofix -> *)
  (*   let types := fix_context mfix in *)
  (*   nth_error mfix n = Some decl -> *)
  (*   ∥ wf_local Σ (Γ ,,, types) ∥ -> *)
  (*   All (fun d => ∥ Σ;;; Γ ,,, types |- dbody d : (lift0 #|types|) (dtype d) ∥) mfix -> *)
  (*   ∥ Σ;;; Γ |- tCoFix mfix n : dtype decl ∥. *)
  (* Proof. *)
  (*   intros H types H0 H1 H2. *)
  (*   apply All_sq in H2. sq. *)
  (*   eapply type_CoFix; eauto. *)
  (* Defined. *)

  Program Fixpoint infer (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term) {struct t}
    : typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ }) :=
    match t with
    | tRel n =>
          match nth_error Γ n with
          | Some c => ret ((lift0 (S n)) (decl_type c); _)
          | None   => raise (UnboundRel n)
          end

    | tVar n  => raise (UnboundVar n)
    | tEvar ev args => raise (UnboundEvar ev)

    | tSort u =>
          match u with
          | NEL.sing (l, false) =>
            check_eq_true (LevelSet.mem l (global_ext_levels Σ)) (Msg "undeclared level");;
            ret (tSort (Universe.super l); _)
          | _ => raise (UnboundVar "not a level")
          end

    | tProd na A B =>
          s1 <- infer_type infer Γ HΓ A ;;
          s2 <- infer_type infer (Γ ,, vass na A) _ B ;;
          ret (tSort (Universe.sort_of_product s1.π1 s2.π1); _)

    | tLambda na A t =>
          s1 <- infer_type infer Γ HΓ A ;;
          B <- infer (Γ ,, vass na A) _ t ;;
          ret (tProd na A B.π1; _)

    | tLetIn n b b_ty b' =>
          infer_type infer Γ HΓ b_ty ;;
          infer_cumul infer Γ HΓ b b_ty _ ;;
          b'_ty <- infer (Γ ,, vdef n b b_ty) _ b' ;;
          ret (tLetIn n b b_ty b'_ty.π1; _)

    | tApp t u =>
          ty <- infer Γ HΓ t ;;
          pi <- reduce_to_prod Γ ty.π1 _ ;;
          infer_cumul infer Γ HΓ u pi.π2.π1 _ ;;
          ret (subst10 u pi.π2.π2.π1; _)

    | tConst cst u =>
          match lookup_env (fst Σ) cst with
          | Some (ConstantDecl _ d) =>
            check_consistent_constraints d.(cst_universes) u ;;
            let ty := subst_instance_constr u d.(cst_type) in
            ret (ty; _)
          |  _ => raise (UndeclaredConstant cst)
          end

    | tInd ind u =>
          d <- lookup_ind_decl ind ;;
          check_consistent_constraints d.π1.(ind_universes) u ;;
          let ty := subst_instance_constr u d.π2.π1.(ind_type) in
          ret (ty; _)

    | tConstruct ind k u =>
          d <- lookup_ind_decl ind ;;
          match nth_error d.π2.π1.(ind_ctors) k with
          | Some cdecl =>
            check_consistent_constraints d.π1.(ind_universes) u ;;
            ret (type_of_constructor d.π1 cdecl (ind, k) u; _)
          | None => raise (UndeclaredConstructor ind k)
          end

    | tCase (ind, par) p c brs =>
      cty <- infer Γ HΓ c ;;
      I <- reduce_to_ind Γ cty.π1 _ ;;
      let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
      check_eq_true (eqb ind ind')
                    (NotConvertible' Γ (tInd ind u) (tInd ind' u)) ;;
      d <- lookup_ind_decl ind' ;;
      let '(decl; d') := d in let '(body; HH) := d' in
      check_eq_true (ind_npars decl =? par)
                    (Msg "not the right number of parameters") ;;
      pty <- infer Γ HΓ p ;;
      match types_of_case ind decl body (firstn par args) u p pty.π1 with
      | None => raise (Msg "not the type of a case")
      | Some (indctx, pctx, ps, btys) =>
        check_eq_true
          (check_correct_arity body ind u indctx (firstn par args) pctx)
          (Msg "not correct arity") ;;
        match Exists_dec (fun sf  => universe_family ps = sf) (ind_kelim body)
                         (sort_family_eqdec _) with
        | right _ => raise (Msg "cannot eliminate over this sort")
        | left x => (fix check_branches (brs btys : list (nat * term)) (HH : Forall (fun A => wellformed Σ Γ (snd A)) btys) {struct brs}
   : typing_result
       (All2 (fun x y => fst x = fst y /\ ∥ Σ ;;; Γ |- snd x : snd y ∥) brs btys)
                    := match brs, btys with
                       | [], [] => ret (All2_nil _)
                       | (n, t) :: brs , (m, A) :: btys =>
                         W <- check_dec (Msg "not nat eq") (EqDecInstances.nat_eqdec n m) ;;
                         Z <- infer_cumul infer Γ HΓ t A _ ;;
                         X <- check_branches brs btys _ ;;
                         ret (All2_cons _ _ _ _ _ (conj _ _) X)
                       | [], _ :: _
                       | _ :: _, [] => raise (Msg "wrong number of branches")
                       end) brs btys _ ;;
          ret (mkApps p (List.skipn par args ++ [c]); _)
        end
      end

    | tProj (ind, n, k) c =>
          d <- lookup_ind_decl ind ;;
          match nth_error d.π2.π1.(ind_projs) k with
          | Some pdecl =>
            c_ty <- infer Γ HΓ c ;;
            I <- reduce_to_ind Γ c_ty.π1 _ ;;
            let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
            check_eq_true (eqb ind ind')
                          (NotConvertible' Γ (tInd ind u) (tInd ind' u)) ;;
            check_eq_true (ind_npars d.π1 =? n)
                          (Msg "not the right number of parameters") ;;
            check_eq_true (#|args| =? ind_npars d.π1) (* probably redundant *)
                          (Msg "not the right number of parameters") ;;
            let ty := snd pdecl in
            ret (subst0 (c :: List.rev args) (subst_instance_constr u ty);
                   _)
          | None => raise (Msg "projection not found")
          end

    | tFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <- (fix check_types (mfix : mfixpoint term) acc (Hacc : ∥ wf_local_rel Σ Γ acc ∥) {struct mfix}
              : typing_result (∥ wf_local_rel Σ (Γ ,,, acc) (fix_context_i #|acc| mfix) ∥)
              := match mfix with
                 | [] => ret (sq wf_local_rel_nil)
                 | def :: mfix =>
       (* probably not tail recursive but needed so that next line terminates *)
                   W <- infer_type infer Γ HΓ (dtype def) ;;
                   let W' := weakening_sq acc _ _ W.π2 in
                   Z <- check_types mfix
                     (acc ,, vass (dname def) ((lift0 #|acc|) (dtype def)))
                     (wf_local_rel_abs_sq Hacc (W.π1; W')) ;;
                   ret (wf_local_rel_app_inv_sq
                          (wf_local_rel_abs_sq (sq wf_local_rel_nil) (W.π1; W')) Z)
                 end)
           mfix [] (sq wf_local_rel_nil);;
        YY <- (fix check_bodies (mfix' : mfixpoint term)
                  (XX' : ∥ wf_local_rel Σ Γ (fix_context mfix') ∥) {struct mfix'}
 : typing_result (All (fun d =>
 ∥ Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d) ∥
   /\ isLambda (dbody d) = true) mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) _ ;;
                   W2 <- check_eq_true (isLambda (dbody def))
                                      (UnboundVar "not a lambda") ;;
                   Z <- check_bodies mfix' _ ;;
                   ret (All_cons (conj W1 W2) Z)
                 end) mfix _ ;;
        guarded <- check_eq_true (fix_guard mfix) (Msg "Unguarded fixpoint") ;;
        ret (dtype decl; _)
      end


    | tCoFix mfix n =>
      (* to add when generalizing to all flags *)
      allowcofix <- check_eq_true allow_cofix (Msg "cofix not allowed") ;;
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <- (fix check_types (mfix : mfixpoint term) acc (Hacc : ∥ wf_local_rel Σ Γ acc ∥) {struct mfix}
              : typing_result (∥ wf_local_rel Σ (Γ ,,, acc) (fix_context_i #|acc| mfix) ∥)
              := match mfix with
                 | [] => ret (sq wf_local_rel_nil)
                 | def :: mfix =>
       (* probably not tail recursive but needed so that next line terminates *)
                   W <- infer_type infer Γ HΓ (dtype def) ;;
                   let W' := weakening_sq acc _ _ W.π2 in
                   Z <- check_types mfix
                     (acc ,, vass (dname def) ((lift0 #|acc|) (dtype def)))
                     (wf_local_rel_abs_sq Hacc (W.π1; W')) ;;
                   ret (wf_local_rel_app_inv_sq
                          (wf_local_rel_abs_sq (sq wf_local_rel_nil) (W.π1; W')) Z)
                 end)
           mfix [] (sq wf_local_rel_nil);;
        YY <- (fix check_bodies (mfix' : mfixpoint term) (XX' : ∥ wf_local_rel Σ Γ (fix_context mfix') ∥) {struct mfix'}
 : typing_result (All (fun d =>
 ∥ Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d) ∥
   ) mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) _ ;;
                   Z <- check_bodies mfix' _ ;;
                   ret (All_cons W1 Z)
                 end) mfix _ ;;
        ret (dtype decl; _)
      end
    end.

  Next Obligation. sq; now econstructor. Defined.
  Next Obligation. sq; econstructor; tas.
                   now apply LevelSetFact.mem_2. Defined.
  (* tProd *)
  Next Obligation. sq; econstructor; cbn; easy. Defined.
  Next Obligation. sq; econstructor; eassumption. Defined.
  (* tLambda *)
  Next Obligation. sq; econstructor; cbn; easy. Defined.
  Next Obligation. sq; econstructor; eassumption. Defined.
  (* tLetIn *)
  Next Obligation. left; sq; econstructor; eauto. Defined.
  Next Obligation. sq; econstructor; cbn; eauto. Defined.
  Next Obligation. sq; now econstructor. Defined.

  (* tApp *)
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation.
    sq. left. eapply type_reduction in X1; try eassumption.
    eapply validity_term in X1; try assumption. destruct X1.
    - destruct i as [ctx [s [H1 H2]]]. cbn in H1.
      apply destArity_app_Some in H1. destruct H1 as [ctx' [e1 e2]]; subst.
      rewrite app_context_assoc in H2; cbn in H2.
      apply wf_local_app in H2.
      destruct (wf_local_inv H2 _ _ eq_refl) as [_ [u' [HH _]]].
      eexists; exact HH.
    - destruct i as [s HH]. eapply inversion_Prod in HH.
      destruct HH as [s1 [_ [HH _]]]. eexists; eassumption.
  Defined.
  Next Obligation.
    sq; econstructor. 2: eassumption.
    eapply type_reduction; eassumption.
  Defined.

  (* tConst *)
  Next Obligation.
    sq; constructor; try assumption.
    symmetry in Heq_anonymous.
    etransitivity. eassumption.
    now rewrite (lookup_env_id _ _ _ Heq_anonymous).
  Defined.

  (* tInd *)
  Next Obligation. sq; econstructor; eassumption. Defined.

  (* tConstruct *)
  Next Obligation. sq; econstructor; try eassumption. now split. Defined.

  (* tCase *)
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation.
    inversion HH; assumption.
  Qed.
  Next Obligation.
    inversion HH; assumption.
  Qed.
  Next Obligation.
    (* sq. *)
    destruct HΣ, HΓ, X.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    clear Heq_anonymous x X8 H0.
    rename X1 into body, X6 into u, X7 into pars, Heq_anonymous0 into e.
    clear c cty X5 X9.
    symmetry in e. apply Nat.eqb_eq in H1; subst par.
    eapply type_Case_csqce; try eassumption.
    now eapply check_correct_arity_spec.
  Qed.
  Next Obligation.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    assert (∥ All2 (fun x y  => ((fst x = fst y) *
                              (Σ;;; Γ |- snd x : snd y))%type) brs btys ∥). {
      eapply All2_sq. eapply All2_impl. eassumption.
      cbn; intros ? ? []. now sq. }
    destruct HΣ, HΓ, X9, X8, X5, X, H.
    constructor. econstructor; try eassumption.
    - apply beq_nat_true; assumption.
    - symmetry; eassumption.
    - apply check_correct_arity_spec; assumption.
    - eapply type_reduction; eassumption.
  Qed.

  (* tProj *)
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation.
    sq; eapply type_Proj with (pdecl := (i, t0)).
    - split. eassumption. split. symmetry; eassumption. cbn in *.
      now apply beq_nat_true.
    - cbn. destruct (ssrbool.elimT (eqb_spec ind I)); [assumption|].
      eapply type_reduction; eassumption.
    - now apply beq_nat_true.
  Defined.

  (* tFix *)
  Next Obligation. sq; now eapply All_local_env_app_inv. Defined.
  Next Obligation. sq; now eapply All_local_env_app_inv. Defined.
  Next Obligation.
    sq. left. cbn in *.
    apply wf_local_rel_app, fst in XX'. rewrite lift0_p in XX'.
    inversion XX'; subst. destruct X0 as [s HH].
    exists (lift0 #|fix_context mfix| (tSort s)). apply weakening; try assumption.
    apply wf_local_app_inv; assumption.
  Defined.
  Next Obligation.
    clear -XX' HΣ. sq.
    change (wf_local_rel Σ Γ ([vass (dname def) ((lift0 0) (dtype def))] ,,, fix_context_i 1 mfix')) in XX'.
    rewrite lift0_p in XX'.
    pose proof (lift_fix_context mfix' 0 1 0) as e; cbn in e;
      rewrite e in XX' by reflexivity; clear e.
    pose proof (strengthening_wf_local_rel Σ Γ [] [vass (dname def) (dtype def)] (fix_context mfix')) as Y.
    now rewrite !app_context_nil_l in Y.
  Qed.
  Next Obligation.
    assert (∥ All (fun d => ((Σ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d)) * (isLambda (dbody d) = true))%type) mfix ∥). {
      eapply All_sq, All_impl.  exact YY.
      cbn; intros ? []. sq; now constructor. }
    sq; econstructor; try eassumption.
    symmetry; eassumption.
    now eapply All_local_env_app_inv.
  Qed.

  (* tCoFix *)
  Next Obligation. sq; now eapply All_local_env_app_inv. Defined.
  Next Obligation. sq; now eapply All_local_env_app_inv. Defined.
  Next Obligation.
    sq. left. cbn in XX'.
    apply wf_local_rel_app, fst in XX'. rewrite lift0_p in XX'.
    inversion XX'; subst. destruct X0 as [s HH].
    exists (lift0 #|fix_context mfix| (tSort s)). apply weakening; try assumption.
    apply wf_local_app_inv; assumption.
  Defined.
  Next Obligation.
    clear -XX' HΣ. sq.
    change (wf_local_rel Σ Γ ([vass (dname def) ((lift0 0) (dtype def))] ,,, fix_context_i 1 mfix')) in XX'.
    rewrite lift0_p in XX'.
    pose proof (lift_fix_context mfix' 0 1 0) as e; cbn in e;
      rewrite e in XX' by reflexivity; clear e.
    pose proof (strengthening_wf_local_rel Σ Γ [] [vass (dname def) (dtype def)] (fix_context mfix')) as Y.
    now rewrite !app_context_nil_l in Y.
  Defined.
  Next Obligation.
    apply All_sq in YY.
    sq. econstructor; eauto.
    now eapply All_local_env_app_inv.
  Defined.


  Program Definition check Γ (HΓ : ∥ wf_local Σ Γ ∥) t A
    : typing_result (∥ Σ;;; Γ |- t : A ∥) :=
    infer Γ HΓ A ;;
    infer_cumul infer Γ HΓ t A _ ;;
    ret _.
  Next Obligation.
    left. sq. now econstructor.
  Qed.

End Typecheck.

Print Assumptions infer.
(* Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString. *)
(* Extraction infer. *)

Section CheckEnv.
  Context  {cf:checker_flags}.

  Inductive env_error :=
  | IllFormedDecl (e : string) (e : type_error)
  | AlreadyDeclared (id : string).

  Inductive EnvCheck (A : Type) :=
  | CorrectDecl (a : A)
  | EnvError (e : env_error).
  Global Arguments EnvError {A} e.
  Global Arguments CorrectDecl {A} a.

  Instance envcheck_monad : Monad EnvCheck :=
    {| ret A a := CorrectDecl a ;
       bind A B m f :=
         match m with
         | CorrectDecl a => f a
         | EnvError e => EnvError e
         end
    |}.

  Definition wrap_error {A} (id : string) (check : typing_result A) : EnvCheck A :=
    match check with
    | Checked a => CorrectDecl a
    | TypeError e => EnvError (IllFormedDecl id e)
    end.

  Lemma sq_wfl_nil {Σ} : ∥ wf_local Σ [] ∥.
  Proof.
   repeat constructor.
  Qed.

  Definition check_wf_type id Σ HΣ t
    : EnvCheck (∑ u, ∥ Σ;;; [] |- t : tSort u ∥)
    := wrap_error id (@infer_type _ Σ HΣ (@infer _ Σ HΣ) [] sq_wfl_nil t).

  Definition check_wf_judgement id Σ HΣ t ty
    : EnvCheck (∥ Σ;;; [] |- t : ty ∥)
    := wrap_error id (@check _ Σ HΣ [] sq_wfl_nil t ty).

  (* Definition infer_term Σ HΣ t := *)
  (*   wrap_error "" (infer Σ [] t). *)

  (* Definition check_wf_decl Σ (g : global_decl) : EnvCheck () := *)
  (*   match g with *)
  (*   | ConstantDecl id cst => *)
  (*     match cst.(cst_body) with *)
  (*     | Some term => check_wf_judgement id Σ term cst.(cst_type) *)
  (*     | None => check_wf_type id Σ cst.(cst_type) *)
  (*     end *)
  (*   | InductiveDecl id inds => *)
  (*     List.fold_left (fun acc body => *)
  (*                       acc ;; check_wf_type body.(ind_name) Σ body.(ind_type)) *)
  (*                    inds.(ind_bodies) (ret ()) *)
  (*   end. *)

  (* Fixpoint check_fresh id env : EnvCheck () := *)
  (*   match env with *)
  (*   | [] => ret () *)
  (*   | g :: env => *)
  (*     check_fresh id env;; *)
  (*     if eq_constant id (global_decl_ident g) then *)
  (*       EnvError (AlreadyDeclared id) *)
  (*     else ret () *)
  (*   end. *)

  (* Fixpoint check_wf_declarations (φ : uGraph.t) (g : global_declarations) := *)
  (*   match g with *)
  (*   | [] => ret () *)
  (*   | g :: env => *)
  (*     check_wf_declarations φ env ;; *)
  (*     check_wf_decl (env, φ) g ;; *)
  (*     check_fresh (global_decl_ident g) env *)
  (*   end. *)

  (* Definition check_wf_env (Σ : global_context) := *)
  (*   if negb (no_universe_inconsistency (snd Σ)) then *)
  (*     EnvError (AlreadyDeclared "univ inconsistency") (* todo better error *) *)
  (*   else check_wf_declarations (snd Σ) (fst Σ). *)

  (* Definition typecheck_program (p : program) : EnvCheck term := *)
  (*   let Σ := reconstruct_global_context (fst p) in *)
  (*   check_wf_env Σ ;; infer_term Σ (snd p). *)

End CheckEnv.
