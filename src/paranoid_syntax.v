(* Paranoid Syntax

   We propose an implementation of syntax that corresponds to the syntax with
   which this library was designed at first.
   It features all the specifics of the language as mutual inductive types.

   This includes explicit substitutions, seperate syntaxes for types and terms,
   optional Tarski universes and so on...

   This syntax is still configurable. For instance, if you decide not to have
   the Unit type as part of your theory, it will still be part of the syntax,
   but you won't be able to derive that [Γ ⊢ Unit] type or [Γ ⊢ unit : Unit].
*)

Require config tt.

Section ParanoidSyntax.

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
     | ctxextend : context -> type -> context

with type : Type :=
     | Prod : type -> type -> type
     | Id : type -> term -> term -> type
     | Subst : type -> substitution -> type
     | Empty : type
     | Unit : type
     | Bool : type
     | SimProd : type -> type -> type
     | Uni : level -> type
     | El : level -> term -> type

with term : Type :=
     | var : nat -> term
     | lam : type -> type -> term -> term
     | app : term -> type -> type -> term -> term
     | refl : type -> term -> term
     | j : type -> term -> type -> term -> term -> term -> term
     | subst : term -> substitution -> term
     | exfalso : type -> term -> term
     | unit : term
     | true : term
     | false : term
     | cond : type -> term -> term -> term -> term
     | pair : type -> type -> term -> term -> term
     | proj1 : type -> type -> term -> term
     | proj2 : type -> type -> term -> term
     | uniProd : level -> level -> term -> term -> term
     | uniId : level -> term -> term -> term -> term
     | uniEmpty : level -> term
     | uniUnit : level -> term
     | uniBool : nat -> term
     | uniSimProd : level -> level -> term -> term -> term
     | uniUni : level -> term

with substitution : Type :=
     | sbzero : type -> term -> substitution
     | sbweak : type -> substitution
     | sbshift : type -> substitution -> substitution
     | sbid : substitution
     | sbcomp : substitution -> substitution -> substitution
.

Definition exactly : forall {F A}, A -> config.Flag F -> A :=
  fun {F A} a f => a.

Local Instance Syntax : config.Syntax := {|
  config.context      := context ;
  config.type         := type ;
  config.term         := term ;
  config.substitution := substitution ;
  config.level        := level ;

  config.uni  := exactly uni ;
  config.prop := exactly prop ;

  config.ctxempty  := ctxempty ;
  config.ctxextend := ctxextend ;

  config.Prod    := exactly Prod ;
  config.Id      := Id ;
  config.Subst   := Subst ;
  config.Empty   := exactly Empty ;
  config.Unit    := exactly Unit ;
  config.Bool    := exactly Bool ;
  config.SimProd := exactly SimProd ;
  config.Uni     := exactly Uni ;
  config.El      := exactly El  ;

  config.var        := var ;
  config.lam        := exactly lam ;
  config.app        := exactly app ;
  config.refl       := refl ;
  config.j          := exactly j ;
  config.subst      := subst ;
  config.exfalso    := exactly exfalso ;
  config.unit       := exactly unit ;
  config.true       := exactly true  ;
  config.false      := exactly false ;
  config.cond       := exactly cond ;
  config.pair       := exactly pair ;
  config.proj1      := exactly proj1 ;
  config.proj2      := exactly proj2 ;
  config.uniProd    := exactly (exactly uniProd) ;
  (* config.uniId      := exactly (exactly uniId) ; *)
  config.uniId      := exactly uniId ;
  config.uniEmpty   := exactly (exactly uniEmpty) ;
  config.uniUnit    := exactly (exactly uniUnit) ;
  config.uniBool    := exactly (exactly uniBool) ;
  config.uniSimProd := exactly (exactly uniSimProd) ;
  config.uniUni     := exactly uniUni ;

  config.sbzero  := sbzero ;
  config.sbweak  := sbweak ;
  config.sbshift := sbshift ;
  config.sbid    := sbid ;
  config.sbcomp  := sbcomp
|}.

Definition isctx := tt.isctx.
Definition issubst := tt.issubst.
Definition istype := tt.istype.
Definition isterm := tt.isterm.
Definition eqctx := tt.eqctx.
Definition eqsubst := tt.eqsubst.
Definition eqtype := tt.eqtype.
Definition eqterm := tt.eqterm.

End ParanoidSyntax.
