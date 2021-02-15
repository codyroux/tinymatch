Set Implicit Arguments.

(* On importe le module qui definit les listes *)
Require Import List.
Print list.
Print option.

(* Une section permet de declarer des Hypotheses et des Variables *)
Section Typer.

(* On declare un type qui va servir de type des variable *)
Variable Var:Type.

Print sumbool.
(* On suppose que l'egalite sur Var est decidable: il existe une fonction,
   Var_eq_dec telle que:
   Var_eq_dec x y renvoie (left p) si x=y, avec p une preuve de x=y,
   Var_eq_dec x y renvoie (right q) si x=/=y (note x<>y) et q en est une preuve

   Notez qu'on peut ecrire "if Var_eq_dec x y then A else B" et ce terme se reduit
   en A si Var_eq_dec se reduit en "left _" et en B sinon. En pratique donc,
   Var_eq_dec agit comme une fonction d'egalite.
*)

Hypothesis Var_eq_dec: forall (x y:Var), {x=y}+{x<>y}.

(* On declare le type de donnees des termes de notre language*)
Inductive AST:Type :=
|var: Var -> AST
|Succ: AST -> AST
|Zero: AST
|Cons: AST -> AST -> AST
|Nil: AST
|NatMatch: AST -> AST -> Var -> AST -> AST
|ListMatch: AST -> AST -> Var -> Var -> AST -> AST.

(* On definit une coercion: un terme de type Var peut etre (automatiquement) vu
   comme un terme de type AST. *)
Coercion var:Var>->AST.

(* On definit le type des types de notre language*)
Inductive Types:Type:=
|Nat
|ListNat.

(* On prouve que l'egalite des types est decidable.*)
Lemma Types_eq_dec: forall (T U:Types), {T=U}+{T<>U}.
intros; case T; case U; try (right; discriminate); try (left;auto).
Defined.

Eval simpl in (Types_eq_dec Nat Nat).

Eval simpl in (Types_eq_dec Nat ListNat).

(* On definit un jugement comme un couple d'une variable et d'un type*)
Definition Jugmt := (Var*Types)%type.

(* On definit un contexte comme une liste de jugements*)
Definition Ctxt:= list Jugmt.

(* IsIn j G est vrai si et seulement si le jugement j est dans le contexte G *)
(* Remarquez que IsIn (v,T) G est seulement vrai si T correspond au type de la
   premiere occurence de v...*)
Inductive IsIn: Jugmt -> Ctxt -> Prop:=
|isInHd: forall v T l, IsIn (v, T) ((v, T)::l)
|isInTl: forall v T v' T' l, ~(v=v') -> IsIn (v,T) l -> IsIn (v,T) ((v',T')::l).

(* Cette commande permet a la tactique "auto" d'essayer
   les tactiques "apply isInHd" et "apply isInTl" automatiquement*)
Hint Resolve isInHd isInTl.

(* On definit ici le jugement de Typage *)
Inductive IsTypedBy: Ctxt -> AST -> Types -> Prop:=
|varCase: forall G v T, IsIn (v,T) G -> IsTypedBy G v T
|SuccCase: forall G n, IsTypedBy G n Nat -> IsTypedBy G (Succ n) Nat
|ZeroCase: forall G, IsTypedBy G Zero Nat
|ConsCase: forall G n l, IsTypedBy G n Nat -> IsTypedBy G l ListNat 
  -> IsTypedBy G (Cons n l) ListNat
|NilCase: forall G, IsTypedBy G Nil ListNat
|NatMatchCase: forall G t zCase v succCase T, IsTypedBy G t Nat
  -> IsTypedBy G zCase T -> IsTypedBy ((v,Nat)::G) succCase T
  -> IsTypedBy G (NatMatch t zCase v succCase) T
|ListMatchCase: forall G t nilCase v l consCase T, IsTypedBy G t ListNat
  -> IsTypedBy G nilCase T -> ~(v=l) 
  -> IsTypedBy ((v,Nat)::(l,ListNat)::G) consCase T
  -> IsTypedBy G (ListMatch t nilCase v l consCase) T
.

(* On introduit une notation pour rendre plus lisible
   ce jugement *)
Notation "G |-- t :~ T":=(IsTypedBy G t T)(at level 50).

Hint Resolve varCase SuccCase ZeroCase ConsCase NilCase NatMatchCase ListMatchCase.


(* On definit une tactique (ici essenciellement une macro) *)
(* "case" effectue un raisonnement par cas, "congruence" essaye de resoudre
   les buts qui sont constitues d'une egalite entre types inductivs,
   ou, si il y a une hypothese constitue d'une egalite ou d'une inegalite
   entre types inductifs contradictoire, resoud le but.
   "try tac" lance la tactique tac, puis ne fait rien si elle echoue.
   *)
Ltac smartCase t := (case t; try congruence; auto).

(*smartCase' regarde le but. Si c'est un forall x, P, il introduit
   la variable x avec un nom frais, puis applique smartCase avec ce nom*)
Ltac smartCase' := match goal with
                     |[ _:_ |- forall some_variable : _,_] => 
                       let t := fresh "t" in
                       intro t; smartCase t
                   end.

(* encore une macro... *)
Ltac genCase H t:= generalize H; smartCase t; smartCase'.


(* un assignement de variable est un couple variable terme *)
Definition Assigmt:=(Var*AST)%type.

(* un contexte d'evaluation est une liste d'assignements *)
Definition EvalCtxt:=list Assigmt.


(* renvoie le premier assignement d'une variable si il
   en trouve un *)
Fixpoint lookupEnv (v:Var) (env:EvalCtxt):option AST:=
  match env with
    |nil => None
    |(v',t)::env' => if Var_eq_dec v v' then Some t else lookupEnv v env'
  end.


(* la fonction qui evalue un terme dans un contexte
   echoue si:
   - une variable n'est pas dans le contexte
   - un terme matche ne se reduit pas vers un constructeur
   du bon type
*)

Fixpoint eval (env:EvalCtxt)(t:AST): option AST:=
  match t with
    |var v                               => lookupEnv v env
    |Succ n                              => match eval env n with
                                              |Some vn => Some (Succ vn)
                                              |_       => None
                                            end
    |Zero                                => Some Zero
    |Cons n l                            => match (eval env n, eval env l) with
                                              |(Some vn, Some vl) => Some (Cons vn vl)
                                              | _                 => None
                                            end
    |Nil                                 => Some Nil
    |NatMatch n zCase v succCase         => match (eval env n) with
                                              |Some Zero     => eval env zCase
                                              |Some (Succ m) => eval ((v,m)::env) succCase
                                              | _            => None
                                            end
    |ListMatch l nilCase v1 v2 consCase  => match (eval env l) with
                                              |Some Nil         => eval env nilCase
                                              |Some (Cons n ns) => eval ((v1,n)::(v2,ns)::env) consCase
                                              |_                => None
                                            end
end.


(* Value t T denote le fait que t est une valeur
   close de type T
   *)
Inductive Value : AST -> Types -> Prop:=
| valZero : Value Zero Nat
| valSucc : forall n, Value n Nat -> Value (Succ n) Nat
| valNil  : Value Nil ListNat
| valCons : forall n l, Value n Nat -> Value l ListNat -> Value (Cons n l) ListNat.

Notation "t ||- T":=(Value t T)(at level 40).

Hint Resolve valZero valSucc valNil valCons.

(* On doit supposer que les assignations du contexte d'evaluation sont correctes*)
Definition CorrectEvalCtxt (env:EvalCtxt) (G:Ctxt) := forall v T, IsIn (v,T) G -> 
  exists t, lookupEnv v env = Some t /\ t ||- T.

Notation "env ||-- G":=(CorrectEvalCtxt env G)(at level 50).

(* serie de lemmes potentiellement pratiques *)
Lemma correctEvalCtxtNil: nil ||-- nil.
intro.
intros.
inversion H.
Qed.

Lemma isInHdEq: forall v T T' G, IsIn (v,T) ((v,T')::G) -> T=T'.
intros.
inversion H; auto.
congruence.
Qed.

Hint Rewrite isInHdEq:core.

Lemma isInTlInv: forall v v0 T T0 G, v<>v0 -> IsIn (v,T) ((v0,T0)::G) -> IsIn (v,T) G.
intros.
inversion H0; congruence.
Qed.



Lemma evalCtxtExtend: forall G env v val T, env ||-- G -> val ||- T -> 
  ((v,val)::env) ||-- ((v,T)::G).
intros.
intro.
intros.
simpl.
generalize H1.
case (Var_eq_dec v0 v).
intro; rewrite e.
intros.
exists val; intuition.
assert (H3:= @isInHdEq _ _ _ _ H2).
rewrite H3; auto.
intros.
apply H.
apply (@isInTlInv _ v _ T); auto.
Qed.

(* la tactique destrHyp prend des hypotheses et les simplifies pour pouvoir
   les appliquer: un but de la forme "forall x:A,P->Q" est transforme en Q si il y a
   un A et un P dans les hypotheses.
   *)
Ltac remAll:= match goal with
                | [ H0 : ?T, H1 : forall env : ?T,_ |- _ ] => 
                  let H := fresh "H" in
                    generalize (H1 H0); clear H1; intro H
              end.


Ltac remHyp:= match goal with
                | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] =>
                  let H := fresh "H" in
                    generalize (H1 H2); clear H1; intro H
              end.

Ltac destrHyp := remAll; remHyp.

(* simplhyp fait comme destrHyp, mais neccesite des applications explicites *)
Ltac simplHyp h1 h2 h3:= let H := fresh "H" in 
  generalize (h1 h2 h3); clear h1; intro H.

(* Le theoreme de correction s'exprime ainsi: si l'environement envoie des variables 
   sur des valeurs, et qu'un terme t a le type T, alors l'evaluation de ce terme
   termine sur "Some u" pour un certain terme "u", et u est une valeur.

   On prouve donc a la foix la correction et la progression. La terminaison n'est pas
   a prouver, elle est implicitement vraie car la fonction "eval" passe le critere
   de terminaison de Coq.
*)

Theorem correctEval: forall G t T env, env ||-- G -> G |-- t :~ T -> 
  exists val, eval env t = Some val /\ val ||- T.
intros.
generalize H; clear H.
generalize env; clear env.
induction H0; intros.
simpl.
apply H0; auto.

simpl.
destrHyp.
firstorder.
rewrite H1; simpl.
exists (Succ x).
auto.

simpl.
exists Zero; auto.

simpl.
repeat destrHyp.
firstorder.
rewrite H0; simpl.
rewrite H2; simpl.
exists (Cons x0 x); auto.

exists Nil; auto.
simplHyp IHIsTypedBy1 env H.
simplHyp IHIsTypedBy2 env H.
firstorder.
simpl.
rewrite H0.
inversion H2.
exists x0; auto.

apply IHIsTypedBy3.
apply evalCtxtExtend; auto.

simplHyp IHIsTypedBy1 env H0.
simplHyp IHIsTypedBy2 env H0.
firstorder.

simpl.
rewrite H1.
inversion H3.
rewrite H2.
exists x0; auto.

apply IHIsTypedBy3.
apply evalCtxtExtend; auto.
apply evalCtxtExtend; auto.

Qed.

End Typer.

Recursive Extraction eval.


Lemma nat_eq_dec: forall (x y:nat), {x=y}+{x<>y}.

  induction x; induction y; simpl; auto.
  assert (H:=IHx y).
  destruct H.
  left; auto.
  right; auto.
Qed.


Check (@correctEval nat nat_eq_dec).
