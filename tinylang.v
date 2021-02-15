Require Import List.
Print list.
Print option.

(* A delimiter for local variables and hypotheses *)
Section Typer.

(* The type of program variables *)
Variable Var : Type.

(* 
   A natural assumption: equality is decidable.

*)

Hypothesis Var_eq_dec: forall (x y:Var), {x=y}+{x<>y}.

(* The Abstract Syntax Trees of our language *)
Inductive AST:Type :=
|var: Var -> AST
|Succ: AST -> AST
|Zero: AST
|Cons: AST -> AST -> AST
|Nil: AST
(* NatMatch a b x v is "match a with | 0 => b | S x => v(x)" *)
|NatMatch: AST -> AST -> Var -> AST -> AST
|ListMatch: AST -> AST -> Var -> Var -> AST -> AST.

(* Variables have a natural inclusion in terms *)
Coercion var : Var >-> AST.

(* The type of types of programs *)
Inductive Types:Type:=
|Nat
|ListNat.

(* Convenient lemma *)
Lemma Types_eq_dec: forall (T U:Types), {T=U}+{T<>U}.
Proof.
  (* Convenient tactic :) *)
  decide equality.
Defined.

(* A typing judgement is just a pair of a variable and its associated type *)
Definition Jugmt := (Var*Types)%type.

(* And a context is a list of such things *)
Definition Ctxt:= list Jugmt.

(* IsIn j G is true iff j is in the context G. *)
Inductive IsIn: Jugmt -> Ctxt -> Prop:=
|isInHd: forall v T l, IsIn (v, T) ((v, T)::l)
(* We explicitly exclude duplicates *)
|isInTl: forall v T v' T' l, ~(v=v') -> IsIn (v,T) l -> IsIn (v,T) ((v',T')::l).

Infix "" := IsIn (at level 30).

(* A little help for auto. *)
Hint Constructors IsIn.

Reserved Notation "G |-- t :~ T"(at level 50).

(* These are the typing rules *)
Inductive IsTypedBy: Ctxt -> AST -> Types -> Prop:=
|varCase: forall G v T, (v,T)  G -> G |-- v :~ T
|SuccCase: forall G n, G |-- n :~ Nat -> G |-- (Succ n) :~ Nat
|ZeroCase: forall G, G |-- Zero :~ Nat
|ConsCase: forall G n l,
    G |-- n :~ Nat ->
    G |-- l :~ ListNat ->
    G |-- (Cons n l) :~ ListNat
|NilCase: forall G, G |-- Nil :~ ListNat
|NatMatchCase: forall G t zCase v succCase T,
    G |-- t :~ Nat ->
    G |-- zCase :~ T ->
    ((v, Nat) :: G) |-- succCase :~ T ->
    G |-- (NatMatch t zCase v succCase) :~ T
|ListMatchCase: forall G t nilCase v l consCase T,
    v <> l ->
    G |-- t :~ ListNat ->
    G |-- nilCase :~ T ->
    ((v, Nat) :: (l, ListNat) :: G) |-- consCase :~ T ->
    G |-- (ListMatch t nilCase v l consCase) :~ T
where
(* On introduit une notation pour rendre plus lisible
   ce jugement *)
 "G |-- t :~ T":=(IsTypedBy G t T).

Hint Constructors IsTypedBy.


Ltac smartCase t := (case t; try congruence; auto).

Ltac smartCase' := match goal with
                     |[ _:_ |- forall some_variable : _,_] => 
                       let t := fresh "t" in
                       intro t; smartCase t
                   end.

Ltac genCase H t:= generalize H; smartCase t; smartCase'.


(* An assignment is like a judgement, but matches a term to a variable rather than a type. *)
Definition Assigmt:=(Var*AST)%type.

(* Similarly for evaluation contexts/contexts *)
Definition EvalCtxt:=list Assigmt.

(* Returns the first binding of a variable if it exists. *)
Fixpoint lookupEnv (v : Var) (env : EvalCtxt) : option AST :=
  match env with
    |nil => None
    |(v',t)::env' => if Var_eq_dec v v' then Some t else lookupEnv v env'
  end.


(*

  The evaluation function evaluates a term to it's "value" (just
  another term) and fails if

  - A variable is not found in the context

  - a match is performed on an incorrect value.

  Note that this funcition is structurally recursive. This is because
  we don't have any "fancy" concepts, like lambdas or recursion.

 *)

Fixpoint eval (env:EvalCtxt)(t:AST): option AST:=
  match t with
  |var v => lookupEnv v env
  |Succ n =>
   match eval env n with
   |Some vn => Some (Succ vn)
   |_       => None
   end
  |Zero => Some Zero
  |Cons n l =>
   match (eval env n, eval env l) with
   |(Some vn, Some vl) => Some (Cons vn vl)
   | _                 => None
   end
  |Nil => Some Nil
  |NatMatch n zCase v succCase =>
   match (eval env n) with
   |Some Zero     => eval env zCase
   |Some (Succ m) => eval ((v,m)::env) succCase
   | _            => None
   end
  |ListMatch l nilCase v1 v2 consCase =>
   match (eval env l) with
   |Some Nil         => eval env nilCase
   |Some (Cons n ns) => eval ((v1, n) :: (v2, ns) :: env) consCase
   |_                => None
   end
end.


Reserved Notation "t ||- T"(at level 50).

(* A simple type to define the notion of "value of type Foo" *)
Inductive Value : AST -> Types -> Prop:=
| valZero : Zero ||- Nat
| valSucc : forall n, n ||- Nat -> (Succ n) ||- Nat
| valNil  : Nil ||- ListNat
| valCons : forall n l, n ||- Nat -> l ||- ListNat -> (Cons n l) ||- ListNat
where "t ||- T":=(Value t T).

Hint Constructors Value.

(* This assumption is that variables in the (typing) context are to be
found in the evaluation context, and that they map to values. *)
Definition CorrectEvalCtxt (env:EvalCtxt) (G:Ctxt) :=
  forall v T, (v, T)  G ->
  exists t, lookupEnv v env = Some t /\ t ||- T.

Notation "env ||-- G":=(CorrectEvalCtxt env G)(at level 60).

Lemma correctEvalCtxtNil: nil ||-- nil.
Proof.
  intros ? ? h.
  inversion h.
Qed.

Lemma isInHdEq: forall v T T' G, (v, T)  ((v, T') :: G) -> T=T'.
Proof.
  intros ? ? ? ? h.
  inversion h; auto; congruence.
Qed.

Hint Rewrite isInHdEq.

Lemma isInTlInv: forall v v0 T T0 G, v <> v0 -> (v, T)  ((v0, T0) :: G) -> (v, T)  G.
Proof.
  intros ? ? ? ? ? ? h.
  inversion h; auto; congruence.
Qed.


Hint Resolve isInTlInv.

Lemma evalCtxtExtend: forall G env v val T,
    env ||-- G ->
    val ||- T -> 
    ((v, val) :: env) ||-- ((v, T) :: G).
Proof.
  intros G env v val T envh valh.
  unfold "||--"; simpl.
  intros v0 T0.  
  destruct (Var_eq_dec v0 v).
  - rewrite e; intro mem; exists val; split; auto.
    assert (h : T0 = T) by (eapply isInHdEq; eauto).
    rewrite h; now auto.
  - intros h; generalize (isInTlInv _ _ _ _ _ n h).
    apply envh; now auto.
Qed.


Lemma cons_env_ctxt_correct : forall v m T env G,
    m ||- T ->
    env ||-- G ->
    ((v, m) :: env) ||-- ((v, T) :: G).
Proof.
  intros v m T env G.
  unfold "||--".
  intros m_val h v0 T0 mem.
  simpl; destruct (Var_eq_dec v0 v).
  - subst; exists m; simpl.
    assert (h1 : T0 = T) by (eapply isInHdEq; eauto).
    rewrite h1; now auto.
  - apply h; eapply isInTlInv; now eauto.
Qed.

Hint Resolve cons_env_ctxt_correct.

(* 
   Progress and preservation:

*)

Theorem correctEval: forall G t T env,
    G |-- t :~ T ->
    env ||-- G ->
    exists val, eval env t = Some val /\ val ||- T.
Proof.
  intros G t T env typ.
  generalize env; clear env.
  induction typ; simpl; intros env envh.
  - now auto.
  - destruct (IHtyp env) as (v & v_some & v_val); auto.
    exists (Succ v).
    rewrite v_some; simpl; now auto.
  - exists Zero; now auto.
  - destruct (IHtyp1 env) as (nv & nv_some & nv_val); auto.
    destruct (IHtyp2 env) as (lv & lv_some & lv_val); auto.
    exists (Cons nv lv); rewrite nv_some, lv_some.
    now auto.
  - exists Nil; now auto.
  - destruct (IHtyp1 env) as (tv & tv_some & tv_val); auto.
    inversion tv_val; subst.
    + destruct (IHtyp2 env) as (nv & nv_some & nv_val); auto.
      exists nv.
      rewrite tv_some; now auto.
    + destruct (IHtyp3 ((v, n) :: env)) as (nv & nv_some & nv_val); auto.
      rewrite tv_some.
      exists nv; now auto.
  -  destruct (IHtyp1 env) as (tv & tv_some & tv_val); auto.
    inversion tv_val; subst.
    + destruct (IHtyp2 env) as (lv & lv_some & lv_val); auto.
      exists lv.
      rewrite tv_some; now auto.
    + destruct (IHtyp3 ((v, n) :: (l, l0) :: env)) as (lv & lv_some & lv_val); auto.
      rewrite tv_some.
      exists lv; now auto.
Qed.
