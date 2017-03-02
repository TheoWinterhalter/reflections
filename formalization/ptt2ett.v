Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require ptt ett.

Section Ptt2Ett.

Context `{configReflection : config.Reflection}.

Fixpoint sane_isctx G (P : ptt.isctx G) : ett.isctx G

with sane_issubst sbs G D (P : ptt.issubst sbs G D) {struct P} : ett.issubst sbs G D

with sane_istype G A (P : ptt.istype G A) {struct P} : ett.istype G A

with sane_isterm G u A (P : ptt.isterm G u A) {struct P} : ett.isterm G u A

with sane_eqctx G D (P : ptt.eqctx G D) {struct P} : ett.eqctx G D

with sane_eqsubst sbs sbt G D (P : ptt.eqsubst sbs sbt G D) {struct P} : ett.eqsubst sbs sbt G D

with sane_eqtype G A B (P : ptt.eqtype G A B) {struct P} : ett.eqtype G A B

with sane_eqterm G u v A (P : ptt.eqterm G u v A) {struct P} : ett.eqterm G u v A.

Proof.
  all:unfold ett.isctx in *.
  all:unfold ett.issubst in *.
  all:unfold ett.istype in *.
  all:unfold ett.isterm in *.
  all:unfold ett.eqctx in *.
  all:unfold ett.eqsubst in *.
  all:unfold ett.eqtype in *.
  all:unfold ett.eqterm in *.

  (* sane_isctx *)
  - { destruct P; doConfig.
      - now apply CtxEmpty.
      - capply CtxExtend. auto.
    }

  (* sane_issubst *)
  - { destruct P; doConfig.

      (* SubstZero *)
      - capply SubstZero ; auto.

      (* SubstWeak *)
      - capply SubstWeak ; auto.

      (* SubstShift *)
      - { capply SubstShift ; auto. }

      (* SubstId *)
      - capply SubstId ; auto.

      (* SubstComp *)
       - { capply (@SubstComp _ _ G D E) ; auto. }

      (* SubstCtxConv *)
      - { capply (@SubstCtxConv _ _ G1 G2 D1 D2) ; auto. }
  }

  (* sane_istype *)
  - { destruct P; doConfig.

      (* TyCtxConv *)
      - capply (@TyCtxConv _ _ G D) ; auto.

      (* TySubst *)
      - capply (@TySubst _ _ G D) ; auto.

      (* TyProd *)
      - capply TyProd ; auto.

      (* TyId *)
      - capply TyId ; auto.

      (* TyEmpty *)
      - capply TyEmpty ; auto.

      (* TyUnit *)
      - capply TyUnit ; auto.

      (* TyBool *)
      - capply TyBool ; auto.
  }

  (* sane_isterm *)
  - { destruct P; doConfig.

      (* TermTyConv *)
       - apply (@TermTyConv _ _ G A B) ; auto.

      (* TermCtxConv *)
      - apply (@TermCtxConv _ _ G D) ; auto.

      (* TermSubst *)
      - apply (@TermSubst _ _ G D) ; auto.

      (* TermVarZero *)
      - apply TermVarZero ; auto.

      (* TermVarSucc *)
      - apply TermVarSucc ; auto.

      (* TermAbs *)
      - apply TermAbs ; auto.

      (* TermApp *)
      - apply TermApp ; auto.

      (* TermRefl *)
      - apply TermRefl ; auto.

      (* TermJ *)
      - apply TermJ ; auto.

      (* TermExfalso *)
      - apply TermExfalso ; auto.

      (* TermUnit *)
      - apply TermUnit ; auto.

      (* TermTrue *)
      - apply TermTrue ; auto.

      (* TermFalse *)
      - apply TermFalse ; auto.

      (* TermCond *)
      - apply TermCond ; auto.
  }

  (* sane_eqctx *)
  - { destruct P; doConfig.

      (* CtxRefl *)
      - apply CtxRefl ; auto.

      (* CtxSym *)
      - apply CtxSym ; auto.

      (* CtxTrans *)
      - apply (@CtxTrans _ _ G D E) ; auto.

      (* EqCtxEmpty *)
      - apply CtxRefl, CtxEmpty.

      (* EqCtxExtend *)
      - apply EqCtxExtend ; auto.
  }

  (* sane_eqsubst *)
  - { destruct P; doConfig.

      (* SubstRefl *)
      - apply SubstRefl ; auto.

      (* SubstSym *)
      - apply SubstSym ; auto.

      (* SubstTrans *)
      - apply (@SubstTrans _ _ G D sb1 sb2 sb3) ; auto.

      (* CongSubstZero *)
      - apply (@CongSubstZero _ _ G) ; auto.

      (* CongSubstWeak *)
      - apply CongSubstWeak ; auto.

      (* CongSubstShift *)
      - apply CongSubstShift ; auto.

      (* CongSubstComp *)
      - apply (@CongSubstComp _ _ G D E) ; auto.

      (* EqSubstCtxConv *)
      - apply (@EqSubstCtxConv _ _ G1 G2 D1 D2) ; auto.

      (* CompAssoc *)
      - apply (@CompAssoc _ _ G D E F) ; auto.

      (* WeakNat *)
      - apply WeakNat ; auto.

      (* WeakZero *)
      - apply WeakZero ; auto.

      (* ShiftZero *)
      - apply ShiftZero ; auto.

      (* CompShift *)
      - apply (@CompShift _ _ G D) ; auto.

      (* CompIdRight *)
      - apply CompIdRight ; auto.

      (* CompIdLeft *)
      - apply CompIdLeft ; auto.
  }

  (* sane_eqtype *)
  - { destruct P; doConfig.

      (* EqTyCtxConv *)
      - apply (@EqTyCtxConv _ _ G D); auto.

      (* EqTyRefl*)
      - apply EqTyRefl ; auto.

      (* EqTySym *)
      - apply EqTySym ; auto.

      (* EqTyTrans *)
      - apply (@EqTyTrans _ _ G A B C) ; auto.

      (* EqTyIdSubst *)
      - apply EqTyIdSubst ; auto.

      (* EqTySubstComp *)
      - apply (@EqTySubstComp _ _ G D E) ; auto.

      (* EqTySubstProd *)
      - apply (@EqTySubstProd _ _ G D) ; auto.

      (* EqTySubstId *)
      - apply (@EqTySubstId _ _ G D) ; auto.

      (* EqTySubstEmpty *)
      - apply (@EqTySubstEmpty _ _ G D) ; auto.

      (* EqTySubstUnit *)
      - apply (@EqTySubstUnit _ _ G D) ; auto.

      (* EqTySubstBool *)
      - apply (@EqTySubstBool _ _ G D) ; auto.

      (* EqTyExfalso *)
      - apply (@EqTyExfalso _ _ G A B u) ; auto.

      (* CongProd *)
      - apply CongProd ; auto.

      (* CongId *)
      - apply CongId ; auto.

      (* CongTySubst *)
      - apply (@CongTySubst _ _ G D A B sbs sbt) ; auto.
  }

  (* sane_eqterm *)
  - { destruct P ; doConfig.

      (* EqTyConv *)
      - apply (@EqTyConv _ _ G A B) ; auto.

      (* EqCtxConv *)
      - apply (@EqCtxConv _ _ G D) ; auto.

      (* EqRefl *)
      - apply EqRefl ; auto.

      (* EqSym *)
      - apply EqSym ; auto.

      (* EqTrans *)
      - apply (@EqTrans _ _ G A u v w) ; auto.

      (* EqIdSubst *)
      - apply EqIdSubst ; auto.

      (* EqSubstComp *)
      - apply (@EqSubstComp _ _ G D E); auto.

      (* EqSubstWeak *)
      - apply EqSubstWeak ; auto.


      (* EqSubstZeroZero *)
      - apply EqSubstZeroZero ; auto.

      (* EqSubstZeroSucc *)
      - apply EqSubstZeroSucc ; auto.

      (* EqSubstShiftZero *)
      - apply (@EqSubstShiftZero _ _ G D) ; auto.

      (* EqSubstShiftSucc *)
      - apply (@EqSubstShiftSucc _ _ G D) ; auto.

      (* EqSubstAbs *)
      - apply (@EqSubstAbs _ _ G D) ; auto.

      (* EqSubstApp *)
      - apply (@EqSubstApp _ _ G D) ; auto.

      (* EqSubstRefl *)
      - apply (@EqSubstRefl _ _ G D) ; auto.

      (* EqSubstJ *)
      - apply (@EqSubstJ _ _ G D) ; auto.

     (* This rule is subsumed by EqTermExfalso *)
      (* EqSubstExfalso *)
      - apply (@EqSubstExfalso _ _ G D) ; auto.

      (* EqSubstUnit *)
      - apply (@EqSubstUnit _ _ G D) ; auto.

      (* EqSubstTrue *)
      - apply (@EqSubstTrue _ _ G D) ; auto.

      (* EqSubstFalse *)
      - apply (@EqSubstFalse _ _ G D) ; auto.

      (* EqSubstCond *)
      - apply (@EqSubstCond _ _ G D); auto.

      (* EqTermExfalso *)
      - apply (@EqTermExfalso _ _ G A u v w); auto.

      (* UnitEta *)
      - apply UnitEta ; auto.

      (* EqReflection *)
      - apply @EqReflection with (w1 := w1) (w2 := w2) ; auto.

      (* ProdBeta *)
      - apply ProdBeta ; auto.

      (* CondTrue *)
      - apply CondTrue ; auto.

      (* CondFalse *)
      - apply CondFalse ; auto.

      (* ProdEta *)
      - apply ProdEta ; auto.

      (* JRefl *)
      - apply JRefl ; auto.

      (* CongAbs *)
      - apply CongAbs ; auto.

      (* CongApp *)
      - apply CongApp ; auto.

      (* CongRefl *)
      - apply CongRefl ; auto.

      (* CongJ *)
      - apply CongJ ; auto.

      (* CongCond *)
      - apply CongCond ; auto.

      (* CongTermSubst *)
    - apply (@CongTermSubst _ _ G D) ; auto.
    }
Defined.

End Ptt2Ett.