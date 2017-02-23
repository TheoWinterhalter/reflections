Require Import syntax.
Require ptt ett.

Fixpoint sane_isctx G (P : ptt.isctx G) : ett.isctx G

with sane_issubst sbs G D (P : ptt.issubst sbs G D) {struct P} : ett.issubst sbs G D

with sane_istype G A (P : ptt.istype G A) {struct P} : ett.istype G A

with sane_isterm G u A (P : ptt.isterm G u A) {struct P} : ett.isterm G u A

with sane_eqctx G D (P : ptt.eqctx G D) {struct P} : ett.eqctx G D

with sane_eqsubst sbs sbt G D (P : ptt.eqsubst sbs sbt G D) {struct P} : ett.eqsubst sbs sbt G D

with sane_eqtype G A B (P : ptt.eqtype G A B) {struct P} : ett.eqtype G A B

with sane_eqterm G u v A (P : ptt.eqterm G u v A) {struct P} : ett.eqterm G u v A.

Proof.
  (* sane_isctx *)
  - { destruct P.
    - now apply ett.CtxEmpty.
    - apply ett.CtxExtend ; auto using sane_isctx, sane_istype.
    }

  (* sane_issubst *)
  - { destruct P.

      (* SubstZero *)
      - apply ett.SubstZero ; auto.

      (* SubstWeak *)
      - apply ett.SubstWeak ; auto.

      (* SubstShift *)
      - apply ett.SubstShift ; auto.

      (* SubstId *)
      - apply ett.SubstId ; auto.

      (* SubstComp *)
       - apply (@ett.SubstComp G D E) ; auto.

      (* SubstCtxConv *)
      - apply (@ett.SubstCtxConv G1 G2 D1 D2) ; auto.
  }

  (* sane_istype *)
  - { destruct P.

      (* TyCtxConv *)
      - apply (@ett.TyCtxConv G D) ; auto.

      (* TySubst *)
      - apply (@ett.TySubst G D) ; auto.

      (* TyProd *)
      - apply ett.TyProd ; auto.

      (* TyId *)
      - apply ett.TyId ; auto.

      (* TyEmpty *)
      - apply ett.TyEmpty ; auto.

      (* TyUnit *)
      - apply ett.TyUnit ; auto.

      (* TyBool *)
      - apply ett.TyBool ; auto.
  }

  (* sane_isterm *)
  - { destruct P.

      (* TermTyConv *)
       - apply (@ett.TermTyConv G A B) ; auto.

      (* TermCtxConv *)
      - apply (@ett.TermCtxConv G D) ; auto.

      (* TermSubst *)
      - apply (@ett.TermSubst G D) ; auto.

      (* TermVarZero *)
      - apply ett.TermVarZero ; auto.

      (* TermVarSucc *)
      - apply ett.TermVarSucc ; auto.

      (* TermAbs *)
      - apply ett.TermAbs ; auto.

      (* TermApp *)
      - apply ett.TermApp ; auto.

      (* TermRefl *)
      - apply ett.TermRefl ; auto.

      (* TermJ *)
      - apply ett.TermJ ; auto.

      (* TermExfalso *)
      - apply ett.TermExfalso ; auto.

      (* TermUnit *)
      - apply ett.TermUnit ; auto.

      (* TermTrue *)
      - apply ett.TermTrue ; auto.

      (* TermFalse *)
      - apply ett.TermFalse ; auto.

      (* TermCond *)
      - apply ett.TermCond ; auto.
  }

  (* sane_eqctx *)
  - { destruct P.

      (* CtxRefl *)
      - apply ett.CtxRefl ; auto.

      (* CtxSym *)
      - apply ett.CtxSym ; auto.

      (* CtxTrans *)
      - apply (@ett.CtxTrans G D E) ; auto.

      (* EqCtxEmpty *)
      - apply ett.CtxRefl, ett.CtxEmpty.

      (* EqCtxExtend *)
      - apply ett.EqCtxExtend ; auto.
  }

  (* sane_eqsubst *)
  - { destruct P.

      (* SubstRefl *)
      - apply ett.SubstRefl ; auto.

      (* SubstSym *)
      - apply ett.SubstSym ; auto.

      (* SubstTrans *)
      - apply (@ett.SubstTrans G D sb1 sb2 sb3) ; auto.

      (* CongSubstZero *)
      - apply ett.CongSubstZero ; auto.

      (* CongSubstWeak *)
      - apply ett.CongSubstWeak ; auto.

      (* CongSubstShift *)
      - apply ett.CongSubstShift ; auto.

      (* CongSubstComp *)
      - apply (@ett.CongSubstComp G D E) ; auto.

      (* EqSubstCtxConv *)
      - apply (@ett.EqSubstCtxConv G1 G2 D1 D2) ; auto.

      (* CompAssoc *)
      - apply (@ett.CompAssoc G D E F) ; auto.

      (* WeakNat *)
      - apply ett.WeakNat ; auto.

      (* WeakZero *)
      - apply @ett.WeakZero with (A := A) ; auto.

      (* ShiftZero *)
      - apply ett.ShiftZero ; auto.

      (* CompShift *)
      - apply @ett.CompShift with (D := D) ; auto.

      (* CompIdRight *)
      - apply ett.CompIdRight ; auto.

      (* CompIdLeft *)
      - apply ett.CompIdLeft ; auto.
  }

  (* sane_eqtype *)
  - { destruct P.

      (* EqTyCtxConv *)
      - apply (@ett.EqTyCtxConv G D); auto.

      (* EqTyRefl*)
      - apply ett.EqTyRefl ; auto.

      (* EqTySym *)
      - apply ett.EqTySym ; auto.

      (* EqTyTrans *)
      - apply (@ett.EqTyTrans G A B C) ; auto.

      (* EqTyIdSubst *)
      - apply ett.EqTyIdSubst ; auto.

      (* EqTySubstComp *)
      - apply (@ett.EqTySubstComp G D E) ; auto.

      (* EqTySubstProd *)
      - apply (@ett.EqTySubstProd G D) ; auto.

      (* EqTySubstId *)
      - apply (@ett.EqTySubstId G D) ; auto.

      (* EqTySubstEmpty *)
      - apply (@ett.EqTySubstEmpty G D) ; auto.

      (* EqTySubstUnit *)
      - apply (@ett.EqTySubstUnit G D) ; auto.

      (* EqTySubstBool *)
      - apply (@ett.EqTySubstBool G D) ; auto.

      (* EqTyExfalso *)
      - apply (@ett.EqTyExfalso G A B u) ; auto.

      (* CongProd *)
      - apply ett.CongProd ; auto.

      (* CongId *)
      - apply ett.CongId ; auto.

      (* CongTySubst *)
      - apply (@ett.CongTySubst G D A B sbs sbt) ; auto.
  }

  (* sane_eqterm *)
  - { destruct P.

      (* EqTyConv *)
      - apply (@ett.EqTyConv G A B) ; auto.

      (* EqCtxConv *)
      - apply (@ett.EqCtxConv G D) ; auto.

      (* EqRefl *)
      - apply ett.EqRefl ; auto.

      (* EqSym *)
      - apply ett.EqSym ; auto.

      (* EqTrans *)
      - apply (@ett.EqTrans G A u v w) ; auto.

      (* EqIdSubst *)
      - apply ett.EqIdSubst ; auto.

      (* EqSubstComp *)
      - apply (@ett.EqSubstComp G D E); auto.

      (* EqSubstWeak *)
      - apply ett.EqSubstWeak ; auto.


      (* EqSubstZeroZero *)
      - apply ett.EqSubstZeroZero ; auto.

      (* EqSubstZeroSucc *)
      - apply @ett.EqSubstZeroSucc with (B := B) ; auto.

      (* EqSubstShiftZero *)
      - apply (@ett.EqSubstShiftZero G D) ; auto.

      (* EqSubstShiftSucc *)
      - apply (@ett.EqSubstShiftSucc G D) ; auto.

      (* EqSubstAbs *)
      - apply (@ett.EqSubstAbs G D) ; auto.

      (* EqSubstApp *)
      - apply (@ett.EqSubstApp G D) ; auto.

      (* EqSubstRefl *)
      - apply (@ett.EqSubstRefl G D) ; auto.

      (* EqSubstJ *)
      - apply @ett.EqSubstJ with (D := D) ; auto.

     (* This rule is subsumed by EqTermExfalso *)
      (* EqSubstExfalso *)
      - apply (@ett.EqSubstExfalso G D) ; auto.

      (* EqSubstUnit *)
      - apply (@ett.EqSubstUnit G D) ; auto.

      (* EqSubstTrue *)
      - apply (@ett.EqSubstTrue G D) ; auto.

      (* EqSubstFalse *)
      - apply (@ett.EqSubstFalse G D) ; auto.

      (* EqSubstCond *)
      - apply @ett.EqSubstCond with (D := D) ; auto.

      (* EqTermExfalso *)
      - apply (@ett.EqTermExfalso G A u v w); auto.

      (* UnitEta *)
      - apply ett.UnitEta ; auto.

      (* EqReflection *)
      - apply (@ett.EqReflection G A u v w1 w2); auto.

      (* ProdBeta *)
      - apply ett.ProdBeta ; auto.

      (* CondTrue *)
      - apply ett.CondTrue ; auto.

      (* CondFalse *)
      - apply ett.CondFalse ; auto.

      (* ProdEta *)
      - apply ett.ProdEta ; auto.

      (* JRefl *)
      - apply ett.JRefl ; auto.

      (* CongAbs *)
      - apply ett.CongAbs ; auto.

      (* CongApp *)
      - apply ett.CongApp ; auto.

      (* CongRefl *)
      - apply ett.CongRefl ; auto.

      (* CongJ *)
      - apply ett.CongJ ; auto.

      (* CongCond *)
      - apply ett.CongCond ; auto.

      (* CongTermSubst *)
    - apply (@ett.CongTermSubst G D) ; auto.
    }
Defined.