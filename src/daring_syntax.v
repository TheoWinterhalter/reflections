(* Daring Syntax

   In a similar fashion as the paranoid syntax, or rather in a dual fashion,
   we write a syntax that isn't entirely defined inductively but that offers
   operators that compute or ignore some of the arguments.

   This way, we hope to provide a syntax that doesn't feature any type
   annotation, doesn't distinguish between the syntax of term and the syntax
   of types, has Russel style universes, and meta-substitutions (substitutions
   compute).

   We intend the both of them as a way to express the two extremes that should
   be captured by our formalisation.
*)

Require config tt.

Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.

Section DaringSyntax.

Context {ConfigPrecond : config.Precond}.
Context {ConfigReflection : config.Reflection}.
Context {ConfigSimpleProducts : config.SimpleProducts}.
Context {ConfigProdEta : config.ProdEta}.
Context {ConfigUniverses : config.Universes}.
Context {ConfigWithProp : config.WithProp}.
Context {ConfigWithJ : config.WithJ}.
Context {ConfigEmpty : config.WithEmpty}.
Context {ConfigUnit : config.WithUnit}.
Context {ConfigBool : config.WithBool}.
Context {ConfigPi : config.WithPi}.

(* Universe levels *)
Inductive level : Type :=
| uni : nat -> level
| prop : level
.

Inductive context : Type :=
     | ctxempty : context
     | ctxextend : context -> term -> context

with term : Type :=
     (* Types *)
     | Prod : term -> term -> term
     | Id : term -> term -> term -> term
     | Empty : term
     | Unit : term
     | Bool : term
     | SimProd : term -> term -> term
     | Uni : level -> term
     (* Terms *)
     | var : nat -> term
     | lam : term -> term -> term
     | app : term -> term -> term
     | refl : term -> term
     | j : term -> term -> term -> term -> term -> term -> term
     | exfalso : term -> term -> term
     | unit : term
     | true : term
     | false : term
     | cond : term -> term -> term -> term -> term
     | pair : term -> term -> term -> term -> term
     | proj1 : term -> term -> term -> term
     | proj2 : term -> term -> term -> term
.

(* Substitutions are taken from Siles et al.  *)
Reserved Notation " t ↑ x # n " (at level 5, x at level 0, left associativity).

Fixpoint lift_rec (n : nat) (k : nat) (t : term) {struct t}
  := match t with
     | Prod A B => Prod (A ↑ n # k) (B ↑ n # (S k))
     | Id A u v => Id (A ↑ n # k) (u ↑ n # k) (v ↑ n # k)
     | Empty => Empty
     | Unit => Unit
     | Bool => Bool
     | SimProd A B => SimProd (A ↑ n # k) (B ↑ n # k)
     | Uni l => Uni l

     | var x => if le_gt_dec k x then var (n + x) else var x
     | lam A t => lam (A ↑ n # k) (t ↑ n # (S k))
     | app u v => app (u ↑ n # k) (v ↑ n # k)
     | refl u => refl (u ↑ n # k)
     | j A u C w v p =>
       j (A ↑ n # k) (u ↑ n # k) (C ↑ n # (S (S k)))
         (w ↑ n # k) (v ↑ n # k) (p ↑ n # k)
     | exfalso A u => exfalso (A ↑ n # k) (u ↑ n # k)
     | unit => unit
     | true => true
     | false => false
     | cond C u v w =>
       cond (C ↑ n # (S k)) (u ↑ n # k) (v ↑ n # k) (w ↑ n # k)
     | pair A B u v =>
       pair (A ↑ n # k) (B ↑ n # k) (u ↑ n # k) (v ↑ n # k)
     | proj1 A B p =>
       proj1 (A ↑ n # k) (B ↑ n # k) (p ↑ n # k)
     | proj2 A B p =>
       proj2 (A ↑ n # k) (B ↑ n # k) (p ↑ n # k)
     end
where "t ↑ n # k" := (lift_rec n k t).

Notation " t ↑ n " := (lift_rec n 0 t)
                        (at level 5, n at level 0, left associativity).
Notation " t ↑ " := (lift_rec 1 0 t) (at level 5, left associativity).

Reserved Notation "t [ x ← u ]" (at level 5, x at level 0, left associativity).

Fixpoint subst_rec u t n {struct t} :=
  match t with
  | Prod A B => Prod (A [n ← u]) (B [S n ← u])
  | Id A a b => Id (A [n ← u]) (a [n ← u]) (b [n ← u])
  | Empty => Empty
  | Unit => Unit
  | Bool => Bool
  | SimProd A B => SimProd (A [n ← u]) (B [n ← u])
  | Uni l => Uni l

  | var x => match (lt_eq_lt_dec x n) with
            | inleft (left _) => var x (* x < n *)
            | inleft (right _) => u ↑ n  (* x = n *)
            | inright _ => var (x - 1) (* x > n *)
            end
  | lam A t => lam (A [n ← u]) (t [S n ← u])
  | app a b => app (a [n ← u]) (b [n ← u])
  | refl t => refl (t [n ← u])
  | j A a C w v p =>
    j (A [n ← u]) (a [n ← u]) (C [S (S n) ← u])
      (w [n ← u]) (v [n ← u]) (p [n ← u])
  | exfalso A a => exfalso (A [n ← u]) (a [n ← u])
  | unit => unit
  | true => true
  | false => false
  | cond C a b c => cond (C [S n ← u]) (a [n ← u]) (b [n ← u]) (c [n ← u])
  | pair A B a b =>
    pair (A [n ← u]) (B [n ← u]) (a [n ← u]) (b [n ← u])
  | proj1 A B p =>
    proj1 (A [n ← u]) (B [n ← u]) (p [n ← u])
  | proj2 A B p =>
    proj2 (A [n ← u]) (B [n ← u]) (p [n ← u])
  end
where " t [ n ← u ] " := (subst_rec u t n).

Notation " t [ ← u ] " := (subst_rec u t 0) (at level 5).

(* Applies σ to every variable subterm above n *)
Fixpoint sbshift σ t n {struct t} :=
  match t with
  | Prod A B => Prod (sbshift σ A n) (sbshift σ B (S n))
  | Id A u v => Id (sbshift σ A n) (sbshift σ u n) (sbshift σ v n)
  | Empty => Empty
  | Unit => Unit
  | Bool => Bool
  | SimProd A B => SimProd (sbshift σ A n) (sbshift σ B n)
  | Uni l => Uni l

  | var x => if le_gt_dec n x then var x else σ (var x)
  | lam A t => lam (sbshift σ A n) (sbshift σ t n)
  | app a b => app (sbshift σ a n) (sbshift σ b n)
  | refl t => refl (sbshift σ t n)
  | j A a C w v p =>
    j (sbshift σ A n) (sbshift σ a n) (sbshift σ C (S (S n)))
      (sbshift σ w n) (sbshift σ v n) (sbshift σ p n)
  | exfalso A a => exfalso (sbshift σ A n) (sbshift σ a n)
  | unit => unit
  | true => true
  | false => false
  | cond C a b c =>
    cond (sbshift σ C n) (sbshift σ a n) (sbshift σ b n) (sbshift σ c n)
  | pair A B a b =>
    pair (sbshift σ A n) (sbshift σ B n) (sbshift σ a n) (sbshift σ b n)
  | proj1 A B p =>
    proj1 (sbshift σ A n) (sbshift σ B n) (sbshift σ p n)
  | proj2 A B p =>
    proj2 (sbshift σ A n) (sbshift σ B n) (sbshift σ p n)
  end.


Definition exactly : forall {F A}, A -> config.Flag F -> A :=
  fun {F A} a f => a.

Local Instance Syntax : config.Syntax := {|
  config.context      := context     ;
  config.type         := term        ;
  config.term         := term        ;
  config.substitution := term -> term ;
  config.level        := level ;

  config.uni := exactly uni ;
  config.prop := exactly prop ;

  config.ctxempty  := ctxempty ;
  config.ctxextend := ctxextend ;

  config.Prod := exactly Prod ;
  config.Id        := Id  ;
  config.Subst A σ := σ A ;
  config.Empty := exactly Empty ;
  config.Unit := exactly Unit ;
  config.Bool := exactly Bool ;
  config.SimProd := exactly SimProd ;
  config.Uni := exactly Uni ;
  config.El  := exactly (fun l A => A)  ;

  config.var       := var    ;
  config.lam := exactly (fun A B t => lam A t) ;
  config.app := exactly (fun u A B v => app u v) ;
  config.refl A u  := refl u ;
  config.j := exactly j ;
  config.subst u σ := σ u    ;
  config.exfalso := exactly exfalso ;
  config.unit := exactly unit ;
  config.true  := exactly true  ;
  config.false := exactly false ;
  config.cond  := exactly cond ;
  config.pair  := exactly pair  ;
  config.proj1 := exactly proj1 ;
  config.proj2 := exactly proj2 ;
  config.uniProd := exactly (exactly (fun l1 l2 A B => Prod A B)) ;
  (* config.uniId := exactly (exactly (fun l A u v => Id A u v)) ; *)
  config.uniId := exactly (fun l A u v => Id A u v) ;
  config.uniEmpty := exactly (exactly (fun l => Empty)) ;
  config.uniUnit := exactly (exactly (fun l => Unit)) ;
  config.uniBool := exactly (exactly (fun l => Bool)) ;
  config.uniSimProd := exactly (exactly (fun l1 l2 A B => SimProd A B)) ;
  config.uniUni := exactly Uni ;

  config.sbzero A u  := fun t => t [ ← u]      ;
  config.sbweak A    := fun t => t ↑           ;
  config.sbshift A σ := fun t => sbshift σ t 0 ;
  config.sbid        := fun t => t             ;
  config.sbcomp σ τ  := fun t => τ (σ t)
|}.


Definition isctx := tt.isctx.
Definition issubst := tt.issubst.
Definition istype := tt.istype.
Definition isterm := tt.isterm.
Definition eqctx := tt.eqctx.
Definition eqsubst := tt.eqsubst.
Definition eqtype := tt.eqtype.
Definition eqterm := tt.eqterm.

End DaringSyntax.
