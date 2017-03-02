(* Confgurable type theory. *)

Require Import syntax.
Require Import config.

Section TypeTheoryRules.
(* Notations for writing down inference rules. *)

Context `{ConfigPrecond : config.Precond}.
Context `{ConfigReflection : config.Reflection}.

Notation "'rule' r 'endrule'" := (r) (at level 96, only parsing).

Notation "'extensional' r" :=
  (forall { _ : reflectionFlag }, r) (only parsing, at level 97).

Notation "'parameters:'  x .. y , p" :=
  ((forall x , .. (forall y , p) ..))
    (at level 200, x binder, y binder, right associativity, only parsing).
Notation "'premise:' p q" := (p -> q) (only parsing, at level 95).
Notation "'precond:' p q" := ((precondFlag -> p) -> q) (only parsing, at level 95).
Notation "'conclusion:' q" := q (no associativity, only parsing, at level 94).

Inductive isctx : context -> Type :=

     | CtxEmpty :
       rule
         conclusion: isctx ctxempty
       endrule

     | CtxExtend :
       rule
         parameters: {G A},
         precond: isctx G
         premise: istype G A
         conclusion: isctx (ctxextend G A)
       endrule


with issubst : substitution -> context -> context -> Type :=

     | SubstZero :
         rule
           parameters: {G u A},
           premise: isterm G u A
           precond: istype G A
           precond: isctx G
           conclusion:
             issubst (sbzero A u) G (ctxextend G A)
         endrule

     | SubstWeak :
       rule
         parameters: {G A},
         premise: istype G A
         precond: isctx G
         conclusion:
           issubst (sbweak A) (ctxextend G A) G
       endrule

     | SubstShift :
       rule
         parameters: {G D A sbs},
         premise: issubst sbs G D
         premise: istype D A
         precond: isctx G
         precond: isctx D
         conclusion:
           issubst (sbshift A sbs)
                   (ctxextend G (Subst A sbs))
                   (ctxextend D A)
       endrule

     | SubstId :
       rule
         parameters: {G},
         premise: isctx G
         conclusion: issubst sbid G G
       endrule

     | SubstComp :
       rule
         parameters: {G D E sbs sbt},
         premise: issubst sbs G D
         premise: issubst sbt D E
         precond: isctx G
         precond: isctx D
         precond: isctx E
         conclusion:
           issubst (sbcomp sbt sbs) G E
       endrule

     | SubstCtxConv :
       rule
         parameters: {G1 G2 D1 D2 sbs},
         premise: issubst sbs G1 D1
         premise: eqctx G1 G2
         premise: eqctx D1 D2
         precond: isctx G1
         precond: isctx G2
         precond: isctx D1
         precond: isctx D2
         conclusion:
           issubst sbs G2 D2
       endrule


with istype : context -> type -> Type :=

     | TyCtxConv :
       rule
         parameters: {G D A},
         premise: istype G A
         premise: eqctx G D
         precond: isctx G
         precond: isctx D
         conclusion:
           istype D A
       endrule

     | TySubst :
       rule
         parameters: {G D A sbs},
         premise: issubst sbs G D
         premise: istype D A
         precond: isctx G
         precond: isctx D
         conclusion:
           istype G (Subst A sbs)
       endrule

     | TyProd :
       rule
         parameters: {G A B},
         premise: istype (ctxextend G A) B
         precond: istype G A
         precond: isctx G
         conclusion:
           istype G (Prod A B)
       endrule

     | TyId :
       rule
         parameters: {G A u v},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         premise: isterm G v A
         conclusion:
           istype G (Id A u v)
       endrule

     | TyEmpty :
       rule
         parameters: {G},
         premise: isctx G
         conclusion:
           istype G Empty
       endrule

     | TyUnit :
       rule
         parameters: {G},
         premise: isctx G
         conclusion:
           istype G Unit
       endrule

     | TyBool :
       rule
         parameters: {G},
         premise: isctx G
         conclusion:
           istype G Bool
       endrule



with isterm : context -> term -> type -> Type :=

     | TermTyConv :
       rule
         parameters: {G A B u},
         premise: isterm G u A
         premise: eqtype G A B
         precond: isctx G
         precond: istype G A
         precond: istype G B
         conclusion:
           isterm G u B
       endrule

     | TermCtxConv :
       rule
         parameters: {G D A u},
         premise: isterm G u A
         premise: eqctx G D
         precond: isctx G
         precond: isctx D
         precond: istype G A
         conclusion:
           isterm D u A
       endrule

     | TermSubst :
       rule
         parameters: {G D A u sbs},
         premise: issubst sbs G D
         premise: isterm D u A
         precond: isctx G
         precond: istype D A
         precond: isctx D
         conclusion:
           isterm G (subst u sbs) (Subst A sbs)
       endrule

     | TermVarZero :
       rule
         parameters: {G A},
         precond: isctx G
         premise: istype G A
         conclusion:
           isterm (ctxextend G A) (var 0) (Subst A (sbweak A))
       endrule

     | TermVarSucc :
       rule
         parameters: {G A B k},
         precond: isctx G
         precond: istype G A
         premise: isterm G (var k) A
         premise: istype G B
         conclusion:
           isterm (ctxextend G B) (var (S k)) (Subst A (sbweak B))
       endrule

     | TermAbs :
       rule
         parameters: {G A u B},
         precond: isctx G
         precond: istype G A
         precond: istype (ctxextend G A) B
         premise: isterm (ctxextend G A) u B
         conclusion:
           isterm G (lam A B u) (Prod A B)
       endrule

     | TermApp :
       rule
         parameters: {G A B u v},
         precond: isctx G
         precond: istype G A
         precond: istype (ctxextend G A) B
         premise: isterm G u (Prod A B)
         premise: isterm G v A
         conclusion:
           isterm G (app u A B v) (Subst B (sbzero A v))
       endrule

     | TermRefl :
       rule
         parameters: {G A u},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         conclusion:
           isterm G (refl A u) (Id A u u)
       endrule

     | TermJ :
       rule
         parameters: {G A C u v w p},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         premise: istype
             (ctxextend
                (ctxextend G A)
                (Id
                   (Subst A (sbweak A))
                   (subst u (sbweak A))
                   (var 0)
                )
             )
             C
         premise:
           isterm G
                  w
                  (Subst
                     (Subst
                        C
                        (sbshift
                           (Id
                              (Subst A (sbweak A))
                              (subst u (sbweak A))
                              (var 0)
                           )
                           (sbzero A u)
                        )
                     )
                     (sbzero (Id A u u) (refl A u))
                  )
         premise: isterm G v A
         premise: isterm G p (Id A u v)
         conclusion:
           isterm G
                  (j A u C w v p)
                  (Subst
                     (Subst
                        C
                        (sbshift
                           (Id
                              (Subst A (sbweak A))
                              (subst u (sbweak A))
                              (var 0)
                           )
                           (sbzero A v)
                        )
                     )
                     (sbzero (Id A u v) p)
                  )
       endrule

     | TermExfalso :
       rule
         parameters: {G A u},
         precond: isctx G
         premise: istype G A
         premise: isterm G u Empty
         conclusion:
           isterm G (exfalso A u) A
       endrule

     | TermUnit :
       rule
         parameters: {G},
         premise: isctx G
         conclusion:
           isterm G unit Unit
       endrule

     | TermTrue :
       rule
         parameters: {G},
         premise: isctx G
         conclusion:
           isterm G true Bool
       endrule

     | TermFalse :
       rule
         parameters: {G},
         premise: isctx G
         conclusion:
           isterm G false Bool
       endrule

     | TermCond :
       rule
         parameters: {G C u v w},
         precond: isctx G
         premise: isterm G u Bool
         premise: istype (ctxextend G Bool) C
         premise: isterm G v (Subst C (sbzero Bool true))
         premise: isterm G w (Subst C (sbzero Bool false))
         conclusion:
           isterm G
                  (cond C u v w)
                  (Subst C (sbzero Bool u))
       endrule



with eqctx : context -> context -> Type :=


     | CtxRefl :
       rule
         parameters: {G},
         premise: isctx G
         conclusion:
           eqctx G G
       endrule

     | CtxSym :
       rule
         parameters: {G D},
         premise: eqctx G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqctx D G
       endrule

     | CtxTrans :
       rule
         parameters: {G D E},
         precond: isctx G
         precond: isctx D
         precond: isctx E
         premise: eqctx G D
         premise: eqctx D E
         conclusion:
           eqctx G E
       endrule

     | EqCtxEmpty :
       rule
         conclusion:
           eqctx ctxempty ctxempty
       endrule

     | EqCtxExtend :
       rule
         parameters: {G D A B},
         precond: isctx G
         precond: isctx D
         precond: istype G A
         precond: istype G B
         premise: eqctx G D
         premise: eqtype G A B
         conclusion:
           eqctx (ctxextend G A) (ctxextend D B)
       endrule

with eqsubst : substitution -> substitution -> context -> context -> Type :=

     | SubstRefl :
       rule
         parameters: {G D sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         conclusion:
           eqsubst sbs sbs G D
       endrule

     | SubstSym :
       rule
         parameters: {G D sbs sbt},
         premise: eqsubst sbs sbt G D
         precond: issubst sbs G D
         precond: issubst sbt G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqsubst sbt sbs G D
       endrule

     | SubstTrans :
       rule
         parameters: {G D sb1 sb2 sb3},
         premise: eqsubst sb1 sb2 G D
         premise: eqsubst sb2 sb3 G D
         precond: issubst sb1 G D
         precond: issubst sb2 G D
         precond: issubst sb3 G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqsubst sb1 sb3 G D
       endrule

     | CongSubstZero :
       rule
         parameters: {G A1 A2 u1 u2},
         premise: eqtype G A1 A2
         premise: eqterm G u1 u2 A1
         precond: isctx G
         precond: istype G A1
         precond: istype G A2
         precond: isterm G u1 A1
         precond: isterm G u2 A1
         conclusion:
           eqsubst (sbzero A1 u1)
                   (sbzero A2 u2)
                   G
                   (ctxextend G A1)
       endrule

     | CongSubstWeak :
       rule
         parameters: {G A1 A2},
         premise: eqtype G A1 A2
         precond: isctx G
         precond: istype G A1
         precond: istype G A2
         conclusion:
           eqsubst (sbweak A1)
                   (sbweak A2)
                   (ctxextend G A1)
                   G
       endrule

     | CongSubstShift :
       rule
         parameters: {G D A1 A2 sbs1 sbs2},
         premise: eqsubst sbs1 sbs2 G D
         premise: eqtype D A1 A2
         precond: isctx G
         precond: isctx D
         precond: istype D A1
         precond: istype D A2
         precond: issubst sbs1 G D
         precond: issubst sbs2 G D
         conclusion:
           eqsubst (sbshift A1 sbs1)
                   (sbshift A2 sbs2)
                   (ctxextend G (Subst A1 sbs1))
                   (ctxextend D A1)
       endrule

     | CongSubstComp :
       rule
         parameters: {G D E sbs1 sbs2 sbt1 sbt2},
         premise: eqsubst sbs1 sbs2 G D
         premise: eqsubst sbt1 sbt2 D E
         precond: issubst sbs1 G D
         precond: issubst sbs2 G D
         precond: issubst sbt1 D E
         precond: issubst sbt2 D E
         precond: isctx G
         precond: isctx D
         precond: isctx E
         conclusion:
           eqsubst (sbcomp sbt1 sbs1)
                   (sbcomp sbt2 sbs2)
                   G
                   E
       endrule

     | EqSubstCtxConv :
       rule
         parameters: {G1 G2 D1 D2 sbs sbt},
         premise: eqsubst sbs sbt G1 D1
         premise: eqctx G1 G2
         premise: eqctx D1 D2
         precond: isctx G1
         precond: isctx G2
         precond: isctx D1
         precond: isctx D2
         precond: issubst sbs G1 D1
         precond: issubst sbt G1 D1
         conclusion:
           eqsubst sbs sbt G2 D2
       endrule

     | CompAssoc :
       rule
         parameters: {G D E F sbs sbt sbr},
         premise: issubst sbs G D
         premise: issubst sbt D E
         premise: issubst sbr E F
         precond: isctx G
         precond: isctx D
         precond: isctx E
         precond: isctx F
         conclusion:
           eqsubst (sbcomp sbr (sbcomp sbt sbs))
                   (sbcomp (sbcomp sbr sbt) sbs)
                   G
                   F
       endrule

     | WeakNat :
       rule
         parameters: {G D A sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         premise: istype D A
         conclusion:
           eqsubst (sbcomp (sbweak A)
                           (sbshift A sbs))
                   (sbcomp sbs
                           (sbweak (Subst A sbs)))
                   (ctxextend G (Subst A sbs))
                   D
       endrule

     | WeakZero :
       rule
         parameters: {G A u},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         conclusion:
           eqsubst (sbcomp (sbweak A) (sbzero A u))
                   sbid
                   G
                   G
       endrule

     | ShiftZero :
       rule
         parameters: {G D A u sbs},
         precond: isctx G
         precond: isctx D
         precond: istype D A
         premise: issubst sbs G D
         premise: isterm D u A
         conclusion:
           eqsubst (sbcomp (sbshift A sbs)
                           (sbzero (Subst A sbs) (subst u sbs)))
                   (sbcomp (sbzero A u)
                           sbs)
                   G
                   (ctxextend D A)
       endrule

     | CompShift :
       rule
         parameters: {G D E A sbs sbt},
         precond: isctx G
         precond: isctx D
         precond: isctx E
         premise: issubst sbs G D
         premise: issubst sbt D E
         premise: istype E A
         conclusion:
           eqsubst (sbcomp (sbshift A sbt)
                           (sbshift (Subst A sbt) sbs))
                   (sbshift A (sbcomp sbt sbs))
                   (ctxextend G (Subst A (sbcomp sbt sbs)))
                   (ctxextend E A)
       endrule

     | CompIdRight :
       rule
         parameters: {G D sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         conclusion:
           eqsubst (sbcomp sbs sbid) sbs G D
       endrule

     | CompIdLeft :
       rule
         parameters: {G D sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         conclusion:
           eqsubst (sbcomp sbid sbs) sbs G D
       endrule


with eqtype : context -> type -> type -> Type :=

     | EqTyCtxConv :
       rule
         parameters: {G D A B},
         premise: eqtype G A B
         premise: eqctx G D
         precond: istype G A
         precond: istype G B
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype D A B
       endrule

     | EqTyRefl:
       rule
         parameters: {G A},
         precond: isctx G
         premise: istype G A
         conclusion:
           eqtype G A A
       endrule

     | EqTySym :
       rule
         parameters: {G A B},
         premise: eqtype G A B
         precond: istype G A
         precond: istype G B
         precond: isctx G
         conclusion:
           eqtype G B A
       endrule

     | EqTyTrans :
       rule
         parameters: {G A B C},
         premise: eqtype G A B
         premise: eqtype G B C
         precond: isctx G
         precond: istype G A
         precond: istype G B
         precond: istype G C
         conclusion:
           eqtype G A C
       endrule

     | EqTyIdSubst :
       rule
         parameters: {G A},
         precond: isctx G
         premise: istype G A
         conclusion:
           eqtype G
                  (Subst A sbid)
                  A
       endrule

     | EqTySubstComp :
       rule
         parameters: {G D E A sbs sbt},
         premise: istype E A
         premise: issubst sbs G D
         premise: issubst sbt D E
         precond: isctx G
         precond: isctx D
         precond: isctx E
         conclusion:
           eqtype G
                  (Subst (Subst A sbt) sbs)
                  (Subst A (sbcomp sbt sbs))
       endrule


     | EqTySubstProd :
       rule
         parameters: {G D A B sbs},
         premise: issubst sbs G D
         precond: istype D A
         premise: istype (ctxextend D A) B
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (Subst (Prod A B) sbs)
                  (Prod (Subst A sbs) (Subst B (sbshift A sbs)))
       endrule

     | EqTySubstId :
       rule
         parameters: {G D A u v sbs},
         premise: issubst sbs G D
         precond: istype D A
         premise: isterm D u A
         premise: isterm D v A
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (Subst (Id A u v) sbs)
                  (Id (Subst A sbs) (subst u sbs) (subst v sbs))
       endrule

     | EqTySubstEmpty :
       rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (Subst Empty sbs)
                  Empty
       endrule

     | EqTySubstUnit :
       rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (Subst Unit sbs)
                  Unit
       endrule

     | EqTySubstBool :
       rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (Subst Bool sbs)
                  Bool
       endrule

     | EqTyExfalso :
       rule
         parameters: {G A B u},
         precond: isctx G
         premise: istype G A
         premise: istype G B
         premise: isterm G u Empty
         conclusion:
           eqtype G A B
       endrule

     | CongProd :
       rule
         parameters: {G A1 A2 B1 B2},
         precond: isctx G
         precond: istype G A1
         precond: istype (ctxextend G A1) A2
         precond: istype G B1
         precond: istype (ctxextend G A1) B2
         premise: eqtype G A1 B1
         premise: eqtype (ctxextend G A1) A2 B2
         conclusion:
           eqtype G (Prod A1 A2) (Prod B1 B2)
       endrule

     | CongId :
       rule
         parameters: {G A B u1 u2 v1 v2},
         precond: isctx G
         precond: istype G A
         precond: istype G B
         precond: isterm G u1 A
         precond: isterm G u2 A
         precond: isterm G v1 A
         precond: isterm G v2 A
         premise: eqtype G A B
         premise: eqterm G u1 v1 A
         premise: eqterm G u2 v2 A
         conclusion:
           eqtype G (Id A u1 u2) (Id B v1 v2)
       endrule

     | CongTySubst :
       rule
         parameters: {G D A B sbs sbt},
         premise: eqsubst sbs sbt G D
         premise: eqtype D A B
         precond: isctx G
         precond: isctx D
         precond: istype D A
         precond: istype D B
         precond: issubst sbs G D
         precond: issubst sbt G D
         conclusion:
           eqtype G (Subst A sbs) (Subst B sbt)
       endrule


with eqterm : context -> term -> term -> type -> Type :=

     | EqTyConv :
       rule
         parameters: {G A B u v},
         premise: eqterm G u v A
         premise: eqtype G A B
         precond: isctx G
         precond: istype G A
         precond: istype G B
         precond: isterm G u A
         precond: isterm G v A
         conclusion:
           eqterm G u v B
       endrule

     | EqCtxConv :
       rule
         parameters: {G D u v A},
         precond: isctx G
         precond: isctx D
         precond: istype G A
         precond: isterm G u A
         precond: isterm G v A
         premise: eqterm G u v A
         premise: eqctx G D
         conclusion:
           eqterm D u v A
       endrule

     | EqRefl :
       rule
         parameters: {G A u},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         conclusion:
           eqterm G u u A
       endrule

     | EqSym :
       rule
         parameters: {G A u v},
         premise: eqterm G v u A
         precond: isterm G u A
         precond: isterm G v A
         precond: istype G A
         precond: isctx G
         conclusion:
           eqterm G u v A
       endrule

     | EqTrans :
       rule
         parameters: {G A u v w},
         premise: eqterm G u v A
         premise: eqterm G v w A
         precond: isctx G
         precond: istype G A
         precond: isterm G u A
         precond: isterm G v A
         precond: isterm G w A
         conclusion:
           eqterm G u w A
       endrule


     | EqIdSubst :
       rule
         parameters: {G A u},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         conclusion:
           eqterm G
                  (subst u sbid)
                  u
                  A
       endrule

     | EqSubstComp :
       rule
         parameters: {G D E A u sbs sbt},
         premise: isterm E u A
         premise: issubst sbs G D
         premise: issubst sbt D E
         precond: isctx G
         precond: isctx D
         precond: isctx E
         precond: istype E A
         conclusion:
           eqterm G
                  (subst (subst u sbt) sbs)
                  (subst u (sbcomp sbt sbs))
                  (Subst A (sbcomp sbt sbs))
       endrule

     | EqSubstWeak :
       rule
         parameters: {G A B k},
         precond: isctx G
         precond: istype G A
         premise: isterm G (var k) A
         premise: istype G B
         conclusion:
           eqterm (ctxextend G B)
                  (subst (var k) (sbweak B))
                  (var (S k))
                  (Subst A (sbweak B))
       endrule


     | EqSubstZeroZero :
       rule
         parameters: {G u A},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         conclusion:
           eqterm G
                  (subst (var 0) (sbzero A u))
                  u
                  A
       endrule

     | EqSubstZeroSucc :
       rule
         parameters: {G A B u k},
         precond: isctx G
         precond: istype G A
         precond: istype G B
         premise: isterm G (var k) A
         premise: isterm G u B
         conclusion:
           eqterm G
                  (subst (var (S k)) (sbzero B u))
                  (var k)
                  A
       endrule

     | EqSubstShiftZero :
       rule
         parameters: {G D A sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         premise: istype D A
         conclusion:
           eqterm (ctxextend G (Subst A sbs))
                  (subst (var 0) (sbshift A sbs))
                  (var 0)
                  (Subst (Subst A sbs) (sbweak (Subst A sbs)))
       endrule

     | EqSubstShiftSucc :
       rule
         parameters: { G D A B sbs k },
         precond: isctx G
         precond: isctx D
         precond: istype D B
         premise: issubst sbs G D
         premise: isterm D (var k) B
         premise: istype D A
         conclusion:
           eqterm (ctxextend G (Subst A sbs))
                  (subst (var (S k)) (sbshift A sbs))
                  (subst (subst (var k) sbs) (sbweak (Subst A sbs)))
                  (Subst (Subst B sbs) (sbweak (Subst A sbs)))
       endrule

     | EqSubstAbs :
       rule
         parameters: {G D A B u sbs},
         precond: isctx G
         precond: isctx D
         precond: istype D A
         precond: istype (ctxextend D A) B
         premise: isterm (ctxextend D A) u B
         premise: issubst sbs G D
         conclusion:
           eqterm G
                  (subst (lam A B u) sbs)
                  (lam
                     (Subst A sbs)
                     (Subst B (sbshift A sbs))
                     (subst u (sbshift A sbs)))
                  (Prod
                     (Subst A sbs)
                     (Subst B (sbshift A sbs)))
       endrule

     | EqSubstApp :
       rule
         parameters: {G D A B u v sbs},
         precond: isctx G
         precond: isctx D
         precond: istype D A
         precond: istype (ctxextend D A) B
         premise: isterm D u (Prod A B)
         premise: isterm D v A
         premise: issubst sbs G D
         conclusion:
           eqterm G
                  (subst (app u A B v) sbs)
                  (app
                     (subst u sbs)
                     (Subst A sbs)
                     (Subst B (sbshift A sbs))
                     (subst v sbs))
                  (Subst (Subst B (sbzero A v)) sbs)
       endrule

     | EqSubstRefl :
       rule
         parameters: {G D A u sbs},
         premise: issubst sbs G D
         premise: isterm D u A
         precond: isctx G
         precond: isctx D
         precond: istype D A
         conclusion:
           eqterm G
                  (subst (refl A u) sbs)
                  (refl (Subst A sbs) (subst u sbs))
                  (Id (Subst A sbs) (subst u sbs) (subst u sbs))
       endrule

     | EqSubstJ :
       rule
         parameters: {G D A C u v w p sbs},
         precond: isctx G
         precond: isctx D
         precond: istype D A
         premise: issubst sbs G D
         premise: isterm D u A
         premise:
           istype
             (ctxextend
                (ctxextend D A)
                (Id
                   (Subst A (sbweak A))
                   (subst u (sbweak A))
                 (var 0)
                )
             )
             C
         premise:
           isterm D
                  w
                  (Subst
                     (Subst
                        C
                        (sbshift
                           (Id
                              (Subst A (sbweak A))
                              (subst u (sbweak A))
                              (var 0)
                           )
                           (sbzero A u)
                        )
                     )
                     (sbzero (Id A u u) (refl A u))
                  )
         premise: isterm D v A
         premise: isterm D p (Id A u v)
         conclusion:
           eqterm G
                  (subst
                     (j A u C w v p)
                     sbs
                  )
                  (j (Subst A sbs)
                     (subst u sbs)
                     (Subst C
                            (sbshift
                               (Id
                                  (Subst A (sbweak A))
                                  (subst u (sbweak A))
                                  (var 0)
                               )
                               (sbshift A sbs)
                            )
                     )
                     (subst w sbs)
                     (subst v sbs)
                     (subst p sbs)
                  )
                  (Subst
                     (Subst
                        (Subst
                           C
                           (sbshift
                              (Id
                                 (Subst A (sbweak A))
                                 (subst u (sbweak A))
                                 (var 0)
                              )
                              (sbzero A v)
                           )
                        )
                        (sbzero (Id A u v) p)
                     )
                     sbs
                  )
       endrule

     (* This rule is subsumed by EqTermExfalso *)
     | EqSubstExfalso :
       rule
         parameters: {G D A u sbs},
         precond: isctx G
         precond: isctx D
         premise: istype D A
         premise: isterm D u Empty
         premise: issubst sbs G D
         conclusion:
           eqterm G
                  (subst (exfalso A u) sbs)
                  (exfalso (Subst A sbs) (subst u sbs))
                  (Subst A sbs)
       endrule

     | EqSubstUnit :
       rule
         parameters: {G D sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         conclusion:
           eqterm G
                  (subst unit sbs)
                  unit
                  Unit
       endrule

     | EqSubstTrue :
       rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst true sbs)
                  true
                  Bool
       endrule

     | EqSubstFalse :
       rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst false sbs)
                  false
                  Bool
       endrule

     | EqSubstCond :
       rule
         parameters: {G D C u v w sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         premise: isterm D u Bool
         premise: istype (ctxextend D Bool) C (* TODO: could this be a precond? *)
         premise: isterm D v (Subst C (sbzero Bool true))
         premise: isterm D w (Subst C (sbzero Bool false))
         conclusion:
           eqterm G
                  (subst (cond C u v w) sbs)
                  (cond (Subst C (sbshift Bool sbs))
                        (subst u sbs)
                        (subst v sbs)
                        (subst w sbs))
                  (Subst (Subst C (sbzero Bool u)) sbs)
       endrule

     | EqTermExfalso :
       rule
         parameters: {G A u v w},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         premise: isterm G v A
         premise: isterm G w Empty
         conclusion:
           eqterm G u v A
       endrule

     | UnitEta :
       rule
         parameters: {G u v},
         precond: isctx G
         premise: isterm G u Unit
         premise: isterm G v Unit
         conclusion:
           eqterm G u v Unit
       endrule

     | EqReflection :
       extensional rule
         parameters: {G A u v w1 w2},
         precond: isctx G
         precond: istype G A
         precond: isterm G u A
         precond: isterm G v A
         premise: isterm G w1 (Id A u v)
         premise: isterm G w2 (reflective A)
         conclusion:
           eqterm G u v A
       endrule

     | ProdBeta :
       rule
         parameters: {G A B u v},
         precond: isctx G
         precond: istype G A
         precond: istype (ctxextend G A) B
         premise: isterm (ctxextend G A) u B
         premise: isterm G v A
         conclusion:
           eqterm G
                  (app (lam A B u) A B v)
                  (subst u (sbzero A v))
                  (Subst B (sbzero A v))
       endrule

     | CondTrue :
       rule
         parameters: {G C v w},
         precond: isctx G
         premise: istype (ctxextend G Bool) C
         premise: isterm G v (Subst C (sbzero Bool true))
         premise: isterm G w (Subst C (sbzero Bool false))
         conclusion:
           eqterm G
                  (cond C true v w)
                  v
                  (Subst C (sbzero Bool true))
       endrule

     | CondFalse :
       rule
         parameters: {G C v w},
         precond: isctx G
         premise: istype (ctxextend G Bool) C
         premise: isterm G v (Subst C (sbzero Bool true))
         premise: isterm G w (Subst C (sbzero Bool false))
         conclusion:
           eqterm G
                  (cond C false v w)
                  w
                  (Subst C (sbzero Bool false))
       endrule

     | ProdEta :
       rule
         parameters: {G A B u v},
         precond: isctx G
         precond: istype G A
         precond: istype (ctxextend G A) B
         premise: isterm G u (Prod A B)
         premise: isterm G v (Prod A B)
         premise: eqterm (ctxextend G A)
                  (app (subst u (sbweak A))
                       (Subst A (sbweak A))
                       (Subst B (sbshift A (sbweak A)))
                       (var 0))
                  (app (subst v (sbweak A))
                       (Subst A (sbweak A))
                       (Subst B (sbshift A (sbweak A)))
                       (var 0))
                  B
         conclusion:
           eqterm G u v (Prod A B)
       endrule

     | JRefl :
       rule
         parameters: {G A C u w},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         premise: istype
             (ctxextend
                (ctxextend G A)
                (Id
                   (Subst A (sbweak A))
                   (subst u (sbweak A))
                   (var 0)
                )
             )
             C
         premise: isterm G
                  w
                  (Subst
                     (Subst
                        C
                        (sbshift
                           (Id
                              (Subst A (sbweak A))
                              (subst u (sbweak A))
                              (var 0)
                           )
                           (sbzero A u)
                        )
                     )
                     (sbzero (Id A u u) (refl A u))
                  )
         conclusion:
           eqterm G
                  (j A u C w u (refl A u))
                  w
                  (Subst
                     (Subst
                        C
                        (sbshift
                           (Id
                              (Subst A (sbweak A))
                              (subst u (sbweak A))
                              (var 0)
                           )
                           (sbzero A u)
                        )
                     )
                     (sbzero (Id A u u) (refl A u))
                  )
       endrule

     | CongAbs :
       rule
         parameters: {G A1 A2 B1 B2 u1 u2},
         precond: isctx G
         precond: istype G A1
         precond: istype G B1
         precond: istype (ctxextend G A1) A2
         precond: istype (ctxextend G A1) B2
         precond: isterm (ctxextend G A1) u1 A2
         precond: isterm (ctxextend G A1) u2 A2
         premise: eqtype G A1 B1
         premise: eqtype (ctxextend G A1) A2 B2
         premise: eqterm (ctxextend G A1) u1 u2 A2
         conclusion:
           eqterm G
                  (lam A1 A2 u1)
                  (lam B1 B2 u2)
                  (Prod A1 A2)
       endrule

     | CongApp :
       rule
         parameters: {G A1 A2 B1 B2 u1 u2 v1 v2},
         precond: isctx G
         precond: istype G A1
         precond: istype (ctxextend G A1) A2
         precond: istype G B1
         precond: istype (ctxextend G A1) B2
         precond: isterm G u1 (Prod A1 A2)
         precond: isterm G v1 (Prod A1 A2)
         precond: isterm G u2 A1
         precond: isterm G v2 A1
         premise: eqtype G A1 B1
         premise: eqtype (ctxextend G A1) A2 B2
         premise: eqterm G u1 v1 (Prod A1 A2)
         premise: eqterm G u2 v2 A1
         conclusion:
           eqterm G
                  (app u1 A1 A2 u2)
                  (app v1 B1 B2 v2)
                  (Subst A2 (sbzero A1 u2))
       endrule

     | CongRefl :
       rule
         parameters: {G u1 u2 A1 A2},
         precond: isctx G
         precond: istype G A1
         precond: istype G A2
         precond: isterm G u1 A1
         precond: isterm G u2 A1
         premise: eqterm G u1 u2 A1
         premise: eqtype G A1 A2
         conclusion:
           eqterm G
                  (refl A1 u1)
                  (refl A2 u2)
                  (Id A1 u1 u1)
       endrule

     | CongJ :
       rule
         parameters: {G A1 A2 C1 C2 u1 u2 v1 v2 w1 w2 p1 p2},
         precond: isctx G
         precond: istype G A1
         precond: istype G A2
         precond:
           istype
             (ctxextend
                (ctxextend G A1)
                (Id
                   (Subst A1 (sbweak A1))
                   (subst u1 (sbweak A1))
                   (var 0)
                )
             )
             C1
         precond:
           istype
             (ctxextend
                (ctxextend G A1)
                (Id
                   (Subst A1 (sbweak A1))
                   (subst u1 (sbweak A1))
                   (var 0)
                )
             )
             C2
         precond: isterm G u1 A1
         precond: isterm G u2 A1
         precond: isterm G v1 A1
         precond: isterm G v2 A1
         precond: isterm G p1 (Id A1 u1 v1)
         precond: isterm G p2 (Id A1 u1 v1)
         premise: eqtype G A1 A2
         premise: eqterm G u1 u2 A1
         premise:
           eqtype
             (ctxextend
                (ctxextend G A1)
                (Id
                   (Subst A1 (sbweak A1))
                   (subst u1 (sbweak A1))
                   (var 0)
                )
             )
             C1
             C2
         precond:
            isterm G
                  w1
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (Id
                              (Subst A1 (sbweak A1))
                              (subst u1 (sbweak A1))
                              (var 0)
                           )
                           (sbzero A1 u1)
                        )
                     )
                     (sbzero (Id A1 u1 u1) (refl A1 u1))
                  )
         precond:
            isterm G
                  w2
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (Id
                              (Subst A1 (sbweak A1))
                              (subst u1 (sbweak A1))
                              (var 0)
                           )
                           (sbzero A1 u1)
                        )
                     )
                     (sbzero (Id A1 u1 u1) (refl A1 u1))
                  )
         premise:
            eqterm G
                  w1
                  w2
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (Id
                              (Subst A1 (sbweak A1))
                              (subst u1 (sbweak A1))
                              (var 0)
                           )
                           (sbzero A1 u1)
                        )
                     )
                     (sbzero (Id A1 u1 u1) (refl A1 u1))
                  )
         premise: eqterm G v1 v2 A1
         premise: eqterm G p1 p2 (Id A1 u1 v1)
         conclusion:
           eqterm G
                  (j A1 u1 C1 w1 v1 p1)
                  (j A2 u2 C2 w2 v2 p2)
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (Id
                              (Subst A1 (sbweak A1))
                              (subst u1 (sbweak A1))
                              (var 0)
                           )
                           (sbzero A1 v1)
                        )
                     )
                     (sbzero (Id A1 u1 v1) p1)
                  )
       endrule

     (* This rule doesn't seem necessary as subsumed by EqTermexfalso! *)
     (* | CongExfalso : *)
     (*     parameters: {G A B u v}, *)
     (*       eqtype G A B -> *)
     (*       eqterm G u v Empty -> *)
     (*       eqterm G *)
     (*              (exfalso A u) *)
     (*              (exfalso B v) *)
     (*              A *)

     | CongCond :
       rule
         parameters: {G C1 C2 u1 u2 v1 v2 w1 w2},
         precond: isctx G
         precond: istype (ctxextend G Bool) C1
         precond: istype (ctxextend G Bool) C2
         precond: isterm G u1 Bool
         precond: isterm G u2 Bool
         precond: isterm G v1 (Subst C1 (sbzero Bool true))
         precond: isterm G v2 (Subst C1 (sbzero Bool true))
         precond: isterm G w1 (Subst C1 (sbzero Bool false))
         precond: isterm G w2 (Subst C1 (sbzero Bool false))
         premise: eqterm G u1 u2 Bool
         premise: eqtype (ctxextend G Bool) C1 C2
         premise: eqterm G v1 v2 (Subst C1 (sbzero Bool true))
         premise: eqterm G w1 w2 (Subst C1 (sbzero Bool false))
         conclusion:
           eqterm G
                  (cond C1 u1 v1 w1)
                  (cond C2 u2 v2 w2)
                  (Subst C1 (sbzero Bool u1))
       endrule

     | CongTermSubst :
       rule
         parameters: {G D A u1 u2 sbs sbt},
         premise: eqsubst sbs sbt G D
         premise: eqterm D u1 u2 A
         precond: isctx G
         precond: isctx D
         precond: istype D A
         precond: isterm D u1 A
         precond: isterm D u2 A
         precond: issubst sbs G D
         precond: issubst sbt G D
         conclusion:
           eqterm G
                  (subst u1 sbs)
                  (subst u2 sbt)
                  (Subst A sbs)
       endrule.

End TypeTheoryRules.
