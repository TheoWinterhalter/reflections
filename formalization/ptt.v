(* Paranoid type theory. *)

Require Import syntax.

Inductive isctx : context -> Type :=

     | CtxEmpty :
       rule
         conclusion: isctx ctxempty
       endrule

     | CtxExtend :
       rule
         parameters: {G A},
         premise: isctx G
         premise: istype G A
         conclusion: isctx (ctxextend G A)
       endrule


with issubst : substitution -> context -> context -> Type :=

     | SubstZero :
         rule
           parameters: {G u A},
           premise: isterm G u A
           premise: istype G A
           premise: isctx G
           conclusion:
             issubst (sbzero u) G (ctxextend G A)
         endrule

     | SubstWeak :
       rule
         parameters: {G A},
         premise: istype G A
         premise: isctx G
         conclusion:
           issubst sbweak (ctxextend G A) G
       endrule

     | SubstShift :
       rule
         parameters: {G D A sbs},
         premise: issubst sbs G D
         premise: istype D A
         premise: isctx G
         premise: isctx D
         conclusion:
           issubst (sbshift sbs)
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
         premise: isctx G
         premise: isctx D
         premise: isctx E
         conclusion:
           issubst (sbcomp sbt sbs) G E
       endrule

     | SubstCtxConv :
       rule
         parameters: {G1 G2 D1 D2 sbs},
         premise: issubst sbs G1 D1
         premise: eqctx G1 G2
         premise: eqctx D1 D2
         premise: isctx G1
         premise: isctx G2
         premise: isctx D1
         premise: isctx D2
         conclusion:
           issubst sbs G2 D2
       endrule


with istype : context -> type -> Type :=

     | TyCtxConv :
       rule
         parameters: {G D A},
         premise: istype G A
         premise: eqctx G D
         premise: isctx G
         premise: isctx D
         conclusion:
           istype D A
       endrule

     | TySubst :
       rule
         parameters: {G D A sbs},
         premise: issubst sbs G D
         premise: istype D A
         premise: isctx G
         premise: isctx D
         conclusion:
           istype G (Subst A sbs)
       endrule

     | TyProd :
       rule
         parameters: {G A B},
         premise: istype (ctxextend G A) B
         premise: istype G A
         premise: isctx G
         conclusion:
           istype G (Prod A B)
       endrule

     | TyId :
       rule
         parameters: {G A u v},
         premise: isctx G
         premise: istype G A
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
         premise: isctx G
         premise: istype G A
         premise: istype G B
         conclusion:
           isterm G u B
       endrule

     | TermCtxConv :
       rule
         parameters: {G D A u},
         premise: isterm G u A
         premise: eqctx G D
         premise: isctx G
         premise: isctx D
         premise: istype G A
         conclusion:
           isterm D u A
       endrule

     | TermSubst :
       rule
         parameters: {G D A u sbs},
         premise: issubst sbs G D
         premise: isterm D u A
         premise: isctx G
         premise: istype D A
         premise: isctx D
         conclusion:
           isterm G (subst u sbs) (Subst A sbs)
       endrule

     | TermVarZero :
       rule
         parameters: {G A},
         premise: isctx G
         premise: istype G A
         conclusion:
           isterm (ctxextend G A) (var 0) (Subst A sbweak)
       endrule

     | TermVarSucc :
       rule
         parameters: {G A B k},
         premise: isctx G
         premise: istype G A
         premise: isterm G (var k) A
         premise: istype G B
         conclusion:
           isterm (ctxextend G B) (var (S k)) (Subst A sbweak)
       endrule

     | TermAbs :
       rule
         parameters: {G A u B},
         premise: isctx G
         premise: istype G A
         premise: istype (ctxextend G A) B
         premise: isterm (ctxextend G A) u B
         conclusion:
           isterm G (lam A B u) (Prod A B)
       endrule

     | TermApp :
       rule
         parameters: {G A B u v},
         premise: isctx G
         premise: istype G A
         premise: istype (ctxextend G A) B
         premise: isterm G u (Prod A B)
         premise: isterm G v A
         conclusion:
           isterm G (app u A B v) (Subst B (sbzero v))
       endrule

     | TermRefl :
       rule
         parameters: {G A u},
         premise: isctx G
         premise: istype G A
         premise: isterm G u A
         conclusion:
           isterm G (refl A u) (Id A u u)
       endrule

     | TermJ :
       rule
         parameters: {G A C u v w p},
         premise: isctx G
         premise: istype G A
         premise: isterm G u A
         premise: istype
             (ctxextend
                (ctxextend G A)
                (Id
                   (Subst A sbweak)
                   (subst u sbweak)
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
                           (sbzero u)
                        )
                     )
                     (sbzero (refl A u))
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
                           (sbzero v)
                        )
                     )
                     (sbzero p)
                  )
       endrule

     | TermExfalso :
       rule
         parameters: {G A u},
         premise: isctx G
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
         premise: isctx G
         premise: isterm G u Bool
         premise: istype (ctxextend G Bool) C
         premise: isterm G v (Subst C (sbzero true))
         premise: isterm G w (Subst C (sbzero false))
         conclusion:
           isterm G
                  (cond C u v w)
                  (Subst C (sbzero u))
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
         premise: isctx G
         premise: isctx D
         conclusion:
           eqctx D G
       endrule

     | CtxTrans :
       rule
         parameters: {G D E},
         premise: isctx G
         premise: isctx D
         premise: isctx E
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
         premise: isctx G
         premise: isctx D
         premise: istype G A
         premise: istype G B
         premise: eqctx G D
         premise: eqtype G A B
         conclusion:
           eqctx (ctxextend G A) (ctxextend D B)
       endrule

with eqsubst : substitution -> substitution -> context -> context -> Type :=

     | SubstRefl :
       rule
         parameters: {G D sbs},
         premise: isctx G
         premise: isctx D
         premise: issubst sbs G D
         conclusion:
           eqsubst sbs sbs G D
       endrule

     | SubstSym :
       rule
         parameters: {G D sbs sbt},
         premise: eqsubst sbs sbt G D
         premise: issubst sbs G D
         premise: issubst sbt G D
         premise: isctx G
         premise: isctx D
         conclusion:
           eqsubst sbt sbs G D
       endrule

     | SubstTrans :
       rule
         parameters: {G D sb1 sb2 sb3},
         premise: eqsubst sb1 sb2 G D
         premise: eqsubst sb2 sb3 G D
         premise: issubst sb1 G D
         premise: issubst sb2 G D
         premise: issubst sb3 G D
         premise: isctx G
         premise: isctx D
         conclusion:
           eqsubst sb1 sb3 G D
       endrule

     | CongSubstZero :
       rule
         parameters: {G A u1 u2},
         premise: eqterm G u1 u2 A
         premise: isctx G
         premise: istype G A
         premise: isterm G u1 A
         premise: isterm G u2 A
         conclusion:
           eqsubst (sbzero u1)
                   (sbzero u2)
                   G
                   (ctxextend G A)
       endrule

     | CongSubstWeak :
       rule
         parameters: {G A},
         premise: istype G A
         premise: isctx G
         conclusion:
           eqsubst sbweak
                   sbweak
                   (ctxextend G A)
                   G
       endrule

     | CongSubstShift :
       rule
         parameters: {G D A sbs1 sbs2},
         premise: eqsubst sbs1 sbs2 G D
         premise: isctx G
         premise: isctx D
         premise: istype D A
         premise: issubst sbs1 G D
         premise: issubst sbs2 G D
         conclusion:
           eqsubst (sbshift sbs1)
                   (sbshift sbs2)
                   (ctxextend G (Subst A sbs1))
                   (ctxextend D A)
       endrule

     | CongSubstComp :
       rule
         parameters: {G D E sbs1 sbs2 sbt1 sbt2},
         premise: eqsubst sbs1 sbs2 G D
         premise: eqsubst sbt1 sbt2 D E
         premise: issubst sbs1 G D
         premise: issubst sbs2 G D
         premise: issubst sbt1 D E
         premise: issubst sbt2 D E
         premise: isctx G
         premise: isctx D
         premise: isctx E
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
         premise: isctx G1
         premise: isctx G2
         premise: isctx D1
         premise: isctx D2
         premise: issubst sbs G1 D1
         premise: issubst sbt G1 D1
         conclusion:
           eqsubst sbs sbt G2 D2
       endrule

     | CompAssoc :
       rule
         parameters: {G D E F sbs sbt sbr},
         premise: issubst sbs G D
         premise: issubst sbt D E
         premise: issubst sbr E F
         premise: isctx G
         premise: isctx D
         premise: isctx E
         premise: isctx F
         conclusion:
           eqsubst (sbcomp sbr (sbcomp sbt sbs))
                   (sbcomp (sbcomp sbr sbt) sbs)
                   G
                   F
       endrule

     | WeakNat :
       rule
         parameters: {G D A sbs},
         premise: isctx G
         premise: isctx D
         premise: issubst sbs G D
         premise: istype D A
         conclusion:
           eqsubst (sbcomp sbweak
                           (sbshift sbs))
                   (sbcomp sbs
                           sbweak)
                   (ctxextend G (Subst A sbs))
                   D
       endrule

     | WeakZero :
       rule
         parameters: {G A u},
         premise: isctx G
         premise: istype G A
         premise: isterm G u A
         conclusion:
           eqsubst (sbcomp sbweak (sbzero u))
                   sbid
                   G
                   G
       endrule

     | ShiftZero :
       rule
         parameters: {G D A u sbs},
         premise: isctx G
         premise: isctx D
         premise: istype D A
         premise: issubst sbs G D
         premise: isterm D u A
         conclusion:
           eqsubst (sbcomp (sbshift sbs)
                           (sbzero (subst u sbs)))
                   (sbcomp (sbzero u)
                           sbs)
                   G
                   (ctxextend D A)
       endrule

     | CompShift :
       rule
         parameters: {G D E A sbs sbt},
         premise: isctx G
         premise: isctx D
         premise: isctx E
         premise: issubst sbs G D
         premise: issubst sbt D E
         premise: istype E A
         conclusion:
           eqsubst (sbcomp (sbshift sbt)
                           (sbshift sbs))
                   (sbshift (sbcomp sbt sbs))
                   (ctxextend G (Subst A (sbcomp sbt sbs)))
                   (ctxextend E A)
       endrule

     | CompIdRight :
       rule
         parameters: {G D sbs},
         premise: isctx G
         premise: isctx D
         premise: issubst sbs G D
         conclusion:
           eqsubst (sbcomp sbs sbid) sbs G D
       endrule

     | CompIdLeft :
       rule
         parameters: {G D sbs},
         premise: isctx G
         premise: isctx D
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
         premise: istype G A
         premise: istype G B
         premise: isctx G
         premise: isctx D
         conclusion:
           eqtype D A B
       endrule

     | EqTyRefl:
       rule
         parameters: {G A},
         premise: isctx G
         premise: istype G A
         conclusion:
           eqtype G A A
       endrule

     | EqTySym :
       rule
         parameters: {G A B},
         premise: eqtype G A B
         premise: istype G A
         premise: istype G B
         premise: isctx G
         conclusion:
           eqtype G B A
       endrule

     | EqTyTrans :
       rule
         parameters: {G A B C},
         premise: eqtype G A B
         premise: eqtype G B C
         premise: isctx G
         premise: istype G A
         premise: istype G B
         premise: istype G C
         conclusion:
           eqtype G A C
       endrule

     | EqTyIdSubst :
       rule
         parameters: {G A},
         premise: isctx G
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
         premise: isctx G
         premise: isctx D
         premise: isctx E
         conclusion:
           eqtype G
                  (Subst (Subst A sbt) sbs)
                  (Subst A (sbcomp sbt sbs))
       endrule


     | EqTySubstProd :
       rule
         parameters: {G D A B sbs},
         premise: issubst sbs G D
         premise: istype D A
         premise: istype (ctxextend D A) B
         premise: isctx G
         premise: isctx D
         conclusion:
           eqtype G
                  (Subst (Prod A B) sbs)
                  (Prod (Subst A sbs) (Subst B (sbshift sbs)))
       endrule

     | EqTySubstId :
       rule
         parameters: {G D A u v sbs},
         premise: issubst sbs G D
         premise: istype D A
         premise: isterm D u A
         premise: isterm D v A
         premise: isctx G
         premise: isctx D
         conclusion:
           eqtype G
                  (Subst (Id A u v) sbs)
                  (Id (Subst A sbs) (subst u sbs) (subst v sbs))
       endrule

     | EqTySubstEmpty :
       rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         premise: isctx G
         premise: isctx D
         conclusion:
           eqtype G
                  (Subst Empty sbs)
                  Empty
       endrule

     | EqTySubstUnit :
       rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         premise: isctx G
         premise: isctx D
         conclusion:
           eqtype G
                  (Subst Unit sbs)
                  Unit
       endrule

     | EqTySubstBool :
       rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         premise: isctx G
         premise: isctx D
         conclusion:
           eqtype G
                  (Subst Bool sbs)
                  Bool
       endrule

     | EqTyExfalso :
       rule
         parameters: {G A B u},
         premise: isctx G
         premise: istype G A
         premise: istype G B
         premise: isterm G u Empty
         conclusion:
           eqtype G A B
       endrule

     | CongProd :
       rule
         parameters: {G A1 A2 B1 B2},
         premise: isctx G
         premise: istype G A1
         premise: istype (ctxextend G A1) A2
         premise: istype G B1
         premise: istype (ctxextend G A1) B2
         premise: eqtype G A1 B1
         premise: eqtype (ctxextend G A1) A2 B2
         conclusion:
           eqtype G (Prod A1 A2) (Prod B1 B2)
       endrule

     | CongId :
       rule
         parameters: {G A B u1 u2 v1 v2},
         premise: isctx G
         premise: istype G A
         premise: istype G B
         premise: isterm G u1 A
         premise: isterm G u2 A
         premise: isterm G v1 A
         premise: isterm G v2 A
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
         premise: isctx G
         premise: isctx D
         premise: istype D A
         premise: istype D B
         premise: issubst sbs G D
         premise: issubst sbt G D
         conclusion:
           eqtype G (Subst A sbs) (Subst B sbt)
       endrule


with eqterm : context -> term -> term -> type -> Type :=

     | EqTyConv :
       rule
         parameters: {G A B u v},
         premise: eqterm G u v A
         premise: eqtype G A B
         premise: isctx G
         premise: istype G A
         premise: istype G B
         premise: isterm G u A
         premise: isterm G v A
         conclusion:
           eqterm G u v B
       endrule

     | EqCtxConv :
       rule
         parameters: {G D u v A},
         premise: isctx G
         premise: isctx D
         premise: istype G A
         premise: isterm G u A
         premise: isterm G v A
         premise: eqterm G u v A
         premise: eqctx G D
         conclusion:
           eqterm D u v A
       endrule

     | EqRefl :
       rule
         parameters: {G A u},
         premise: isctx G
         premise: istype G A
         premise: isterm G u A
         conclusion:
           eqterm G u u A
       endrule

     | EqSym :
       rule
         parameters: {G A u v},
         premise: eqterm G v u A
         premise: isterm G u A
         premise: isterm G v A
         premise: istype G A
         premise: isctx G
         conclusion:
           eqterm G u v A
       endrule

     | EqTrans :
       rule
         parameters: {G A u v w},
         premise: eqterm G u v A
         premise: eqterm G v w A
         premise: isctx G
         premise: istype G A
         premise: isterm G u A
         premise: isterm G v A
         premise: isterm G w A
         conclusion:
           eqterm G u w A
       endrule


     | EqIdSubst :
       rule
         parameters: {G A u},
         premise: isctx G
         premise: istype G A
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
         premise: isctx G
         premise: isctx D
         premise: isctx E
         premise: istype E A
         conclusion:
           eqterm G
                  (subst (subst u sbt) sbs)
                  (subst u (sbcomp sbt sbs))
                  (Subst A (sbcomp sbt sbs))
       endrule

     | EqSubstWeak :
       rule
         parameters: {G A B k},
         premise: isctx G
         premise: istype G A
         premise: isterm G (var k) A
         premise: istype G B
         conclusion:
           eqterm (ctxextend G B)
                  (subst (var k) sbweak)
                  (var (S k))
                  (Subst A sbweak)
       endrule


     | EqSubstZeroZero :
       rule
         parameters: {G u A},
         premise: isctx G
         premise: istype G A
         premise: isterm G u A
         conclusion:
           eqterm G
                  (subst (var 0) (sbzero u))
                  u
                  A
       endrule

     | EqSubstZeroSucc :
       rule
         parameters: {G A B u k},
         premise: isctx G
         premise: istype G A
         premise: istype G B
         premise: isterm G (var k) A
         premise: isterm G u B
         conclusion:
           eqterm G
                  (subst (var (S k)) (sbzero u))
                  (var k)
                  A
       endrule

     | EqSubstShiftZero :
       rule
         parameters: {G D A sbs},
         premise: isctx G
         premise: isctx D
         premise: issubst sbs G D
         premise: istype D A
         conclusion:
           eqterm (ctxextend G (Subst A sbs))
                  (subst (var 0) (sbshift sbs))
                  (var 0)
                  (Subst (Subst A sbs) sbweak)
       endrule

     | EqSubstShiftSucc :
       rule
         parameters: { G D A B sbs k },
         premise: isctx G
         premise: isctx D
         premise: istype D B
         premise: issubst sbs G D
         premise: isterm D (var k) B
         premise: istype D A
         conclusion:
           eqterm (ctxextend G (Subst A sbs))
                  (subst (var (S k)) (sbshift sbs))
                  (subst (subst (var k) sbs) sbweak)
                  (Subst (Subst B sbs) sbweak)
       endrule

     | EqSubstAbs :
       rule
         parameters: {G D A B u sbs},
         premise: isctx G
         premise: isctx D
         premise: istype D A
         premise: istype (ctxextend D A) B
         premise: isterm (ctxextend D A) u B
         premise: issubst sbs G D
         conclusion:
           eqterm G
                  (subst (lam A B u) sbs)
                  (lam
                     (Subst A sbs)
                     (Subst B (sbshift sbs))
                     (subst u (sbshift sbs)))
                  (Prod
                     (Subst A sbs)
                     (Subst B (sbshift sbs)))
       endrule

     | EqSubstApp :
       rule
         parameters: {G D A B u v sbs},
         premise: isctx G
         premise: isctx D
         premise: istype D A
         premise: istype (ctxextend D A) B
         premise: isterm D u (Prod A B)
         premise: isterm D v A
         premise: issubst sbs G D
         conclusion:
           eqterm G
                  (subst (app u A B v) sbs)
                  (app
                     (subst u sbs)
                     (Subst A sbs)
                     (Subst B (sbshift sbs))
                     (subst v sbs))
                  (Subst (Subst B (sbzero v)) sbs)
       endrule

     | EqSubstRefl :
       rule
         parameters: {G D A u sbs},
         premise: issubst sbs G D
         premise: isterm D u A
         premise: isctx G
         premise: isctx D
         premise: istype D A
         conclusion:
           eqterm G
                  (subst (refl A u) sbs)
                  (refl (Subst A sbs) (subst u sbs))
                  (Id (Subst A sbs) (subst u sbs) (subst u sbs))
       endrule

     | EqSubstJ :
       rule
         parameters: {G D A C u v w p sbs},
         premise: isctx G
         premise: isctx D
         premise: istype D A
         premise: issubst sbs G D
         premise: isterm D u A
         premise:
           istype
             (ctxextend
                (ctxextend D A)
                (Id
                   (Subst A sbweak)
                   (subst u sbweak)
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
                           (sbzero u)
                        )
                     )
                     (sbzero (refl A u))
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
                               (sbshift sbs)
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
                              (sbzero v)
                           )
                        )
                        (sbzero p)
                     )
                     sbs
                  )
       endrule

     (* This rule is subsumed by EqTermExfalso *)
     | EqSubstExfalso :
       rule
         parameters: {G D A u sbs},
         premise: isctx G
         premise: isctx D
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
         premise: isctx G
         premise: isctx D
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
         premise: isctx G
         premise: isctx D
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
         premise: isctx G
         premise: isctx D
         conclusion:
           eqterm G
                  (subst false sbs)
                  false
                  Bool
       endrule

     | EqSubstCond :
       rule
         parameters: {G D C u v w sbs},
         premise: isctx G
         premise: isctx D
         premise: issubst sbs G D
         premise: isterm D u Bool
         premise: istype (ctxextend D Bool) C
         premise: isterm D v (Subst C (sbzero true))
         premise: isterm D w (Subst C (sbzero false))
         conclusion:
           eqterm G
                  (subst (cond C u v w) sbs)
                  (cond (Subst C (sbshift sbs))
                        (subst u sbs)
                        (subst v sbs)
                        (subst w sbs))
                  (Subst (Subst C (sbzero u)) sbs)
       endrule

     | EqTermExfalso :
       rule
         parameters: {G A u v w},
         premise: isctx G
         premise: istype G A
         premise: isterm G u A
         premise: isterm G v A
         premise: isterm G w Empty
         conclusion:
           eqterm G u v A
       endrule

     | UnitEta :
       rule
         parameters: {G u v},
         premise: isctx G
         premise: isterm G u Unit
         premise: isterm G v Unit
         conclusion:
           eqterm G u v Unit
       endrule

     | EqReflection :
       rule
         parameters: {G A u v w1 w2},
         premise: isctx G
         premise: istype G A
         premise: isterm G u A
         premise: isterm G v A
         premise: isterm G w1 (Id A u v)
         premise: isterm G w2 (reflective A)
         conclusion:
           eqterm G u v A
       endrule

     | ProdBeta :
       rule
         parameters: {G A B u v},
         premise: isctx G
         premise: istype G A
         premise: istype (ctxextend G A) B
         premise: isterm (ctxextend G A) u B
         premise: isterm G v A
         conclusion:
           eqterm G
                  (app (lam A B u) A B v)
                  (subst u (sbzero v))
                  (Subst B (sbzero v))
       endrule

     | CondTrue :
       rule
         parameters: {G C v w},
         premise: isctx G
         premise: istype (ctxextend G Bool) C
         premise: isterm G v (Subst C (sbzero true))
         premise: isterm G w (Subst C (sbzero false))
         conclusion:
           eqterm G
                  (cond C true v w)
                  v
                  (Subst C (sbzero true))
       endrule

     | CondFalse :
       rule
         parameters: {G C v w},
         premise: isctx G
         premise: istype (ctxextend G Bool) C
         premise: isterm G v (Subst C (sbzero true))
         premise: isterm G w (Subst C (sbzero false))
         conclusion:
           eqterm G
                  (cond C false v w)
                  w
                  (Subst C (sbzero false))
       endrule

     | ProdEta :
       rule
         parameters: {G A B u v},
         premise: isctx G
         premise: istype G A
         premise: istype (ctxextend G A) B
         premise: isterm G u (Prod A B)
         premise: isterm G v (Prod A B)
         premise: eqterm (ctxextend G A)
                  (app (subst u sbweak)
                       (Subst A sbweak)
                       (Subst B (sbshift sbweak))
                       (var 0))
                  (app (subst v sbweak)
                       (Subst A sbweak)
                       (Subst B (sbshift sbweak))
                       (var 0))
                  B
         conclusion:
           eqterm G u v (Prod A B)
       endrule

     | JRefl :
       rule
         parameters: {G A C u w},
         premise: isctx G
         premise: istype G A
         premise: isterm G u A
         premise: istype
             (ctxextend
                (ctxextend G A)
                (Id
                   (Subst A sbweak)
                   (subst u sbweak)
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
                           (sbzero u)
                        )
                     )
                     (sbzero (refl A u))
                  )
         conclusion:
           eqterm G
                  (j A u C w u (refl A u))
                  w
                  (Subst
                     (Subst
                        C
                        (sbshift
                           (sbzero u)
                        )
                     )
                     (sbzero (refl A u))
                  )
       endrule

     | CongAbs :
       rule
         parameters: {G A1 A2 B1 B2 u1 u2},
         premise: isctx G
         premise: istype G A1
         premise: istype G B1
         premise: istype (ctxextend G A1) A2
         premise: istype (ctxextend G A1) B2
         premise: isterm (ctxextend G A1) u1 A2
         premise: isterm (ctxextend G A1) u2 A2
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
         premise: isctx G
         premise: istype G A1
         premise: istype (ctxextend G A1) A2
         premise: istype G B1
         premise: istype (ctxextend G A1) B2
         premise: isterm G u1 (Prod A1 A2)
         premise: isterm G v1 (Prod A1 A2)
         premise: isterm G u2 A1
         premise: isterm G v2 A1
         premise: eqtype G A1 B1
         premise: eqtype (ctxextend G A1) A2 B2
         premise: eqterm G u1 v1 (Prod A1 A2)
         premise: eqterm G u2 v2 A1
         conclusion:
           eqterm G
                  (app u1 A1 A2 u2)
                  (app v1 B1 B2 v2)
                  (Subst A2 (sbzero u2))
       endrule

     | CongRefl :
       rule
         parameters: {G u1 u2 A1 A2},
         premise: isctx G
         premise: istype G A1
         premise: istype G A2
         premise: isterm G u1 A1
         premise: isterm G u2 A1
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
         premise: isctx G
         premise: istype G A1
         premise: istype G A2
         premise:
           istype
             (ctxextend
                (ctxextend G A1)
                (Id
                   (Subst A1 sbweak)
                   (subst u1 sbweak)
                   (var 0)
                )
             )
             C1
         premise:
           istype
             (ctxextend
                (ctxextend G A1)
                (Id
                   (Subst A1 sbweak)
                   (subst u1 sbweak)
                   (var 0)
                )
             )
             C2
         premise: isterm G u1 A1
         premise: isterm G u2 A1
         premise: isterm G v1 A1
         premise: isterm G v2 A1
         premise: isterm G p1 (Id A1 u1 v1)
         premise: isterm G p2 (Id A1 u1 v1)
         premise: eqtype G A1 A2
         premise: eqterm G u1 u2 A1
         premise:
           eqtype
             (ctxextend
                (ctxextend G A1)
                (Id
                   (Subst A1 sbweak)
                   (subst u1 sbweak)
                   (var 0)
                )
             )
             C1
             C2
         premise:
            isterm G
                  w1
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (sbzero u1)
                        )
                     )
                     (sbzero (refl A1 u1))
                  )
         premise:
            isterm G
                  w2
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (sbzero u1)
                        )
                     )
                     (sbzero (refl A1 u1))
                  )
         premise:
            eqterm G
                  w1
                  w2
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (sbzero u1)
                        )
                     )
                     (sbzero (refl A1 u1))
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
                           (sbzero v1)
                        )
                     )
                     (sbzero p1)
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
         premise: isctx G
         premise: istype (ctxextend G Bool) C1
         premise: istype (ctxextend G Bool) C2
         premise: isterm G u1 Bool
         premise: isterm G u2 Bool
         premise: isterm G v1 (Subst C1 (sbzero true))
         premise: isterm G v2 (Subst C1 (sbzero true))
         premise: isterm G w1 (Subst C1 (sbzero false))
         premise: isterm G w2 (Subst C1 (sbzero false))
         premise: eqterm G u1 u2 Bool
         premise: eqtype (ctxextend G Bool) C1 C2
         premise: eqterm G v1 v2 (Subst C1 (sbzero true))
         premise: eqterm G w1 w2 (Subst C1 (sbzero false))
         conclusion:
           eqterm G
                  (cond C1 u1 v1 w1)
                  (cond C2 u2 v2 w2)
                  (Subst C1 (sbzero u1))
       endrule

     | CongTermSubst :
       rule
         parameters: {G D A u1 u2 sbs sbt},
         premise: eqsubst sbs sbt G D
         premise: eqterm D u1 u2 A
         premise: isctx G
         premise: isctx D
         premise: istype D A
         premise: isterm D u1 A
         premise: isterm D u2 A
         premise: issubst sbs G D
         premise: issubst sbt G D
         conclusion:
           eqterm G
                  (subst u1 sbs)
                  (subst u2 sbt)
                  (Subst A sbs)
       endrule.
