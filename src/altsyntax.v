(* Alternative syntax with names for variables *)

Require Import String.

Definition variable := string.

Inductive context : Type :=
| ctxempty : context
| ctxextend : context -> variable -> type -> context

with type : Type :=
| Prod : variable -> type -> type -> type
| Id : type -> term -> term -> type
| Empty : type
| Unit : type
| Bool : type
| SimProd : type -> type -> type
| Uni : nat -> type
(* TODO: Add a Prop universe *)
| El : term -> type

with term : Type :=
| var : variable -> term
| lam : variable -> type -> type -> term -> term
| app : term -> variable -> type -> type -> term -> term
| refl : type -> term -> term
| j : type -> term -> variable -> variable -> type -> term -> term -> term -> term
| exfalso : type -> term -> term
| unit : term
| true : term
| false : term
| cond : variable -> type -> term -> term -> term -> term
| pair : type -> type -> term -> term -> term
| proj1 : type -> type -> term -> term
| proj2 : type -> type -> term -> term
| uniProd : nat -> variable -> term -> term -> term
| uniId : nat -> term -> term -> term -> term
| uniEmpty : nat -> term
| uniUnit : nat -> term
| uniBool : nat -> term
| uniSimProd : nat -> term -> term -> term
| uniUni : nat -> term.

Open Scope string_scope.

Notation "'·'" := (ctxempty).
Notation "'Π' ( x 'in' A ) → B" := (Prod x A B) (at level 20).
Notation "A → B" := (Prod "_" A B) (at level 20).
Notation "u ≡ v 'in' A" := (Id A u v) (at level 10).
(* Notation "'λ' x 'in' A ⇒ v 'to' B" := (lam x A B v) (at level 19). *)
(* Notation "u '@' [ x 'in' A → B ] v" := (app u x A B v) (at level 19). *)
(* Notation "u '@' [ A → B ] v" := (app u "_" A B v) (at level 19). *)

Close Scope string_scope.
