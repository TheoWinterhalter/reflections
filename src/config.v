(* Definitions of configuration options. *)

(* Use these types to instantiate the configuration type classes below. *)

Inductive Yes : Type := yes.
Inductive No : Type := .

(* Each configurable feature is represented by a type class which contains a
   type.

   To turn on a configuration, provide a type class instance in which the type
   is instantiated to `Yes`.

   To turn off a configuration, provide a type class instance in which the type
   is instantiated to `No`.

   To be ambivalent about a configuration, provide a `Context` with an
   unspecified instance of it. Then your development will be parametrized by it
   automagically.

   You have to make sure that you do not provid *two* instances for the same
   configuration option. The best way to do this is to always make sure that all
   the instances are declatered as [Local].
*)

(* Paranoid mode, include preconditions in rules. *)
Class Precond := {
  precondFlag : Type
}.

(* Dependent products. *)
Class WithPi := {
  withpiFlag : Type
}.

(* Equality reflection. *)
Class Reflection := {
  reflectionFlag : Type
}.

(* Simple binary products. *)
Class SimpleProducts := {
  simpleproductsFlag : Type
}.

(* The eta-rule for functions. *)
Class ProdEta := {
  prodetaFlag : Type
}.

(* Universes *)
Class Universes := {
  universesFlag : Type
}.

(* Impredicative universe of propositions. *)
Class WithProp := {
  withpropFlag : Type
}.

(* J-eliminator. *)
Class WithJ := {
  withjFlag : Type
}.

(* Empty type. *)
Class WithEmpty := {
  withemptyFlag : Type
}.

(* Unit type. *)
Class WithUnit := {
  withunitFlag : Type
}.

(* Boolean type. *)
Class WithBool := {
  withboolFlag : Type
}.

Class Flag (A : Type) := {
  flagProof : A
}.

(* The syntax on which to work. *)
Class Syntax `{Universes, WithProp, WithPi, WithEmpty, WithUnit, WithBool,
               SimpleProducts, WithJ}
  := {
  (* Kinds *)
  context      : Type ;
  type         : Type ;
  term         : Type ;
  substitution : Type ;
  level        : Type ;

  (* Universe levels *)
  uni  : forall {_ : Flag universesFlag}, nat -> level ;
  prop : forall {_ : Flag withpropFlag}, level ;

  (* Context constructors *)
  ctxempty  : context ;
  ctxextend : context -> type -> context ;

  (* Types *)
  Prod    : forall {_ : Flag withpiFlag}, type -> type -> type ;
  Id      : type -> term -> term -> type ;
  Subst   : type -> substitution -> type ;
  Empty   : forall {_ : Flag withemptyFlag}, type ;
  Unit    : forall {_ : Flag withunitFlag}, type ;
  Bool    : forall {_ : Flag withboolFlag}, type ;
  SimProd : forall {_ : Flag simpleproductsFlag}, type -> type -> type ;
  Uni     : forall {_ : Flag universesFlag}, level -> type ;
  El      : forall {_ : Flag universesFlag}, level -> term -> type ;

  (* Terms *)
  var : nat -> term ;
  lam : forall {_ : Flag withpiFlag}, type -> type -> term -> term ;
  app : forall {_ : Flag withpiFlag}, term -> type -> type -> term -> term ;
  refl : type -> term -> term ;
  j : forall {_ : Flag withjFlag}, type -> term -> type -> term -> term -> term -> term ;
  subst : term -> substitution -> term ;
  pair : forall {_ : Flag simpleproductsFlag}, type -> type -> term -> term -> term ;
  proj1 : forall {_ : Flag simpleproductsFlag}, type -> type -> term -> term ;
  proj2 : forall {_ : Flag simpleproductsFlag}, type -> type -> term -> term ;
  exfalso : forall {_ : Flag withemptyFlag}, type -> term -> term ;
  unit : forall {_ : Flag withunitFlag}, term ;
  true : forall {_ : Flag withboolFlag}, term ;
  false : forall {_ : Flag withboolFlag}, term ;
  cond : forall {_ : Flag withboolFlag}, type -> term -> term -> term -> term ;
  uniProd : forall {_ : Flag universesFlag}, forall {_ : Flag withpiFlag},
            level -> level -> term -> term -> term ;
  uniId : forall {_ : Flag universesFlag}, (* forall {_ : Flag withidFlag}, *)
          level -> term -> term -> term -> term ;
  uniEmpty : forall {_ : Flag universesFlag}, forall {_ : Flag withemptyFlag},
             level -> term ;
  uniUnit : forall {_ : Flag universesFlag}, forall {_ : Flag withunitFlag},
             level -> term ;
  uniBool : forall {_ : Flag universesFlag}, forall {_ : Flag withboolFlag},
             nat -> term ;
  uniSimProd : forall {_ : Flag universesFlag}, forall {_ : Flag simpleproductsFlag},
               level -> level -> term -> term -> term ;
  uniUni : forall {_ : Flag universesFlag}, level -> term ;

  (* Explicit substitutions *)
  sbzero  : type -> term -> substitution ;
  sbweak  : type -> substitution ;
  sbshift : type -> substitution -> substitution ;
  sbid    : substitution ;
  sbcomp  : substitution -> substitution -> substitution ;

  (* Notation *)
  Arrow {h : Flag withpiFlag} A B := Prod A (Subst B (sbweak A))
}.
