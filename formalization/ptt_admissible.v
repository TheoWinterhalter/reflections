(* Admissibile ptt rules. *)

Require config.
Require Import config_tactics.
Require Import tt.
Require Import syntax.
Require Import ptt_tactics.

Section PttAdmissible.

Local Instance hasPrecond : config.Precond := {| config.precondFlag := config.Yes |}.
Context `{configReflection : config.Reflection}.

(* Some preliminary lemmata *)
Lemma EqTyWeakNat :
  forall {G D A B sbs},
    issubst sbs G D ->
    istype D A ->
    istype D B ->
    isctx G ->
    isctx D ->
    eqtype (ctxextend G (Subst A sbs))
           (Subst (Subst B (sbweak A)) (sbshift A sbs))
           (Subst (Subst B sbs) (sbweak (Subst A sbs))).
Proof.
  intros. magic.
  Unshelve. all:strictmagic.
Defined.


Lemma compWeakZero :
  forall {G A B u},
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u B ->
    eqtype G A (Subst A (sbcomp (sbweak B) (sbzero B u))).
Proof.
  intros. magic.
Defined.

Lemma EqTyWeakZero :
  forall {G A B u},
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u B ->
    eqtype G A (Subst (Subst A (sbweak B)) (sbzero B u)).
Proof.
  intros. magic.
Defined.

Lemma EqTyShiftZero :
  forall {G D A B v sbs},
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    isterm D v A ->
    isctx G ->
    isctx D ->
    eqtype
      G
      (Subst (Subst B (sbshift A sbs)) (sbzero (Subst A sbs) (subst v sbs)))
      (Subst (Subst B (sbzero A v)) sbs).
Proof.
  intros. magic. Unshelve. all:strictmagic.
Defined.

Lemma EqTyCongZero :
  forall {G A1 A2 B1 B2 u1 u2},
    eqtype (ctxextend G A1) A2 B2 ->
    istype (ctxextend G A1) A2 ->
    istype (ctxextend G A1) B2 ->
    isctx G ->
    eqtype G A1 B1 ->
    eqterm G u1 u2 A1 ->
    istype G A1 ->
    istype G B1 ->
    isterm G u1 A1 ->
    isterm G u2 B1 ->
    eqtype G
           (Subst A2 (sbzero A1 u1))
           (Subst B2 (sbzero B1 u2)).
Proof.
  intros. magic.
Defined.

Lemma EqTyCongShift :
  forall {G D A1 A2 B1 B2 sbs1 sbs2},
    eqsubst sbs1 sbs2 G D ->
    eqtype D A1 A2 ->
    eqtype (ctxextend D A1) B1 B2 ->
    isctx G ->
    isctx D ->
    issubst sbs1 G D ->
    issubst sbs2 G D ->
    istype D A1 ->
    istype D A2 ->
    istype (ctxextend D A1) B1 ->
    istype (ctxextend D A2) B2 ->
    eqtype (ctxextend G (Subst A1 sbs1))
           (Subst B1 (sbshift A1 sbs1))
           (Subst B2 (sbshift A2 sbs2)).
Proof.
  intros. magic.
  Unshelve. all:strictmagic.
Defined.

Lemma EqTyCongWeak :
  forall {G A1 A2 B1 B2},
    eqtype G A1 A2 ->
    eqtype G B1 B2 ->
    isctx G ->
    istype G A1 ->
    istype G B1 ->
    istype G A2 ->
    istype G B2 ->
    eqtype (ctxextend G A1)
           (Subst B1 (sbweak A1))
           (Subst B2 (sbweak A2)).
Proof.
  intros. magic.
Defined.

Lemma EqSubstWeakNat :
  forall {G D A B u sbs},
    issubst sbs G D ->
    istype D A ->
    istype D B ->
    isterm D u B ->
    isctx G ->
    isctx D ->
    eqterm (ctxextend G (Subst A sbs))
           (subst (subst u (sbweak A)) (sbshift A sbs))
           (subst (subst u sbs) (sbweak (Subst A sbs)))
           (Subst (Subst B sbs) (sbweak (Subst A sbs))).
Proof.
  intros. magic.
  Unshelve. all:strictmagic.
Defined.


Lemma EqSubstWeakZero :
  forall {G A B u v},
    istype G A ->
    istype G B ->
    isterm G u A ->
    isterm G v B ->
    isctx G ->
    eqterm G
           (subst (subst u (sbweak B)) (sbzero B v))
           u
           A.
Proof.
  intros. magic.
Defined.

Lemma EqTermShiftZero :
  forall {G D A B u v sbs},
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    isterm (ctxextend D A) u B ->
    isterm D v A ->
    isctx G ->
    isctx D ->
    eqterm
      G
      (subst (subst u (sbshift A sbs)) (sbzero (Subst A sbs) (subst v sbs)))
      (subst (subst u (sbzero A v)) sbs)
      (Subst (Subst B (sbzero A v)) sbs).
Proof.
  intros. magic.
  Unshelve. all:strictmagic.
Defined.

Lemma EqTermCongWeak :
  forall {G A1 A2 B1 B2 u1 u2},
    eqtype G A1 A2 ->
    eqtype G B1 B2 ->
    eqterm G u1 u2 B1 ->
    isctx G ->
    istype G A1 ->
    istype G B1 ->
    istype G B2 ->
    istype G A2 ->
    isterm G u1 B1 ->
    isterm G u2 B2 ->
    eqterm (ctxextend G A1)
           (subst u1 (sbweak A1))
           (subst u2 (sbweak A2))
           (Subst B1 (sbweak A1)).
Proof.
  intros. magic.
Defined.

End PttAdmissible.
