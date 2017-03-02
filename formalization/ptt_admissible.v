(* Admissibile ptt rules. *)

Require Import syntax ptt ptt_tactics.

(* Some preliminary lemmata *)
Lemma EqTyWeakNat :
  forall {G D A B sbs},
    issubst sbs G D ->
    istype D A ->
    istype D B ->
    isctx G ->
    isctx D ->
    eqtype (ctxextend G (Subst A sbs))
           (Subst (Subst B (sbweak D A)) (sbshift G A sbs))
           (Subst (Subst B sbs) (sbweak G (Subst A sbs))).
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
    eqtype G A (Subst A (sbcomp (sbweak G B) (sbzero G B u))).
Proof.
  intros. magic.
Defined.

Lemma EqTyWeakZero :
  forall {G A B u},
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u B ->
    eqtype G A (Subst (Subst A (sbweak G B)) (sbzero G B u)).
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
      (Subst (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
      (Subst (Subst B (sbzero D A v)) sbs).
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
           (Subst A2 (sbzero G A1 u1))
           (Subst B2 (sbzero G B1 u2)).
Proof.
  intros. magic.
Defined.

Lemma EqTyCongShift :
  forall {G1 G2 D A1 A2 B1 B2 sbs1 sbs2},
    eqctx G1 G2 ->
    eqsubst sbs1 sbs2 G1 D ->
    eqtype D A1 A2 ->
    eqtype (ctxextend D A1) B1 B2 ->
    isctx G1 ->
    isctx G2 ->
    isctx D ->
    issubst sbs1 G1 D ->
    issubst sbs2 G2 D ->
    istype D A1 ->
    istype D A2 ->
    istype (ctxextend D A1) B1 ->
    istype (ctxextend D A2) B2 ->
    eqtype (ctxextend G1 (Subst A1 sbs1))
           (Subst B1 (sbshift G1 A1 sbs1))
           (Subst B2 (sbshift G2 A2 sbs2)).
Proof.
  intros. magic.
  Unshelve. all:strictmagic.
Defined.

Lemma EqTyCongWeak :
  forall {G1 G2 A1 A2 B1 B2},
    eqctx G1 G2 ->
    eqtype G1 A1 A2 ->
    eqtype G1 B1 B2 ->
    isctx G1 ->
    isctx G2 ->
    istype G1 A1 ->
    istype G1 B1 ->
    istype G2 A2 ->
    istype G2 B2 ->
    eqtype (ctxextend G1 A1)
           (Subst B1 (sbweak G1 A1))
           (Subst B2 (sbweak G2 A2)).
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
           (subst (subst u (sbweak D A)) (sbshift G A sbs))
           (subst (subst u sbs) (sbweak G (Subst A sbs)))
           (Subst (Subst B sbs) (sbweak G (Subst A sbs))).
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
           (subst (subst u (sbweak G B)) (sbzero G B v))
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
      (subst (subst u (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
      (subst (subst u (sbzero D A v)) sbs)
      (Subst (Subst B (sbzero D A v)) sbs).
Proof.
  intros. magic.
  Unshelve. all:strictmagic.
Defined.

Lemma EqTermCongWeak :
  forall {G1 G2 A1 A2 B1 B2 u1 u2},
    eqctx G1 G2 ->
    eqtype G1 A1 A2 ->
    eqtype G1 B1 B2 ->
    eqterm G1 u1 u2 B1 ->
    isctx G1 ->
    isctx G2 ->
    istype G1 A1 ->
    istype G1 B1 ->
    istype G2 B2 ->
    istype G2 A2 ->
    isterm G1 u1 B1 ->
    isterm G2 u2 B2 ->
    eqterm (ctxextend G1 A1)
           (subst u1 (sbweak G1 A1))
           (subst u2 (sbweak G2 A2))
           (Subst B1 (sbweak G1 A1)).
Proof.
  intros. magic.
Defined.
