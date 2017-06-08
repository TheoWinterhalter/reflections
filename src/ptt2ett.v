Require Import config.
Require Import config_tactics.

Require Import tt.
Require ptt ett.

Section Ptt2Ett.

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

Context {ConfigSyntax : config.Syntax}.

Fixpoint sane_isctx G (P : ptt.isctx G) : ett.isctx G

with sane_issubst sbs G D (P : ptt.issubst sbs G D) {struct P} :
       ett.issubst sbs G D

with sane_istype G A (P : ptt.istype G A) {struct P} : ett.istype G A

with sane_isterm G u A (P : ptt.isterm G u A) {struct P} : ett.isterm G u A

with sane_eqctx G D (P : ptt.eqctx G D) {struct P} : ett.eqctx G D

with sane_eqsubst sbs sbt G D (P : ptt.eqsubst sbs sbt G D) {struct P} :
       ett.eqsubst sbs sbt G D

with sane_eqtype G A B (P : ptt.eqtype G A B) {struct P} : ett.eqtype G A B

with sane_eqterm G u v A (P : ptt.eqterm G u v A) {struct P} :
       ett.eqterm G u v A.

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
       - { config apply @SubstComp with (D := D) ; auto. }

      (* SubstCtxConv *)
      - { config apply @SubstCtxConv with (G1 := G1) (D1 := D1) ; auto. }
  }

  (* sane_istype *)
  - { destruct P; doConfig.

      (* TyCtxConv *)
      - config apply @TyCtxConv with (G := G) ; auto.

      (* TySubst *)
      - config apply @TySubst with (D := D) ; auto.

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

      (* TySimProd *)
      - capply TySimProd ; auto.

      (* TyUni *)
      - capply TyUni ; auto.

      (* TyEl *)
      - ceapply TyEl ; eauto.
  }

  (* sane_isterm *)
  - { destruct P; doConfig.

      (* TermTyConv *)
       - apply @TermTyConv with (A := A) ; auto.

      (* TermCtxConv *)
      - apply @TermCtxConv with (G := G) ; auto.

      (* TermSubst *)
      - apply @TermSubst with (D := D) ; auto.

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

      (* TermPair *)
      - apply TermPair ; auto.

      (* TermProjOne *)
      - apply TermProjOne ; auto.

      (* TermProjTwo *)
      - apply TermProjTwo ; auto.

      (* TermUniProd *)
      - apply TermUniProd ; auto.

      (* TermUniProdProp *)
      - apply TermUniProdProp ; auto.

      (* TermUniId *)
      - apply TermUniId ; auto.

      (* TermUniEmpty *)
      - apply TermUniEmpty ; auto.

      (* TermUniUnit *)
      - apply TermUniUnit ; auto.

      (* TermUniBool *)
      - apply TermUniBool ; auto.

      (* TermUniSimProd *)
      - apply TermUniSimProd ; auto.

      (* TermUniSimProdProp *)
      - apply TermUniSimProdProp ; auto.

      (* TermUniUni *)
      - apply TermUniUni ; auto.

      (* TermUniProp *)
      - apply TermUniProp ; auto.
  }

  (* sane_eqctx *)
  - { destruct P; doConfig.

      (* CtxRefl *)
      - apply CtxRefl ; auto.

      (* CtxSym *)
      - apply CtxSym ; auto.

      (* CtxTrans *)
      - apply @CtxTrans with (D := D) ; auto.

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
      - apply @SubstTrans with (sb2 := sb2) ; auto.

      (* CongSubstZero *)
      - apply @CongSubstZero with (G := G) ; auto.

      (* CongSubstWeak *)
      - apply CongSubstWeak ; auto.

      (* CongSubstShift *)
      - apply CongSubstShift ; auto.

      (* CongSubstComp *)
      - apply @CongSubstComp with (D := D) ; auto.

      (* EqSubstCtxConv *)
      - apply @EqSubstCtxConv with (G1 := G1) (D1 := D1) ; auto.

      (* CompAssoc *)
      - apply @CompAssoc with (D := D) (E := E) ; auto.

      (* WeakNat *)
      - apply WeakNat ; auto.

      (* WeakZero *)
      - apply WeakZero ; auto.

      (* ShiftZero *)
      - apply ShiftZero ; auto.

      (* CompShift *)
      - apply @CompShift with (D := D) ; auto.

      (* CompIdRight *)
      - apply CompIdRight ; auto.

      (* CompIdLeft *)
      - apply CompIdLeft ; auto.
  }

  (* sane_eqtype *)
  - { destruct P; doConfig.

      (* EqTyCtxConv *)
      - apply @EqTyCtxConv with (G := G) ; auto.

      (* EqTyRefl*)
      - apply EqTyRefl ; auto.

      (* EqTySym *)
      - apply EqTySym ; auto.

      (* EqTyTrans *)
      - apply @EqTyTrans with (B := B) ; auto.

      (* EqTyIdSubst *)
      - apply EqTyIdSubst ; auto.

      (* EqTySubstComp *)
      - apply @EqTySubstComp with (D := D) (E := E) ; auto.

      (* EqTySubstProd *)
      - apply @EqTySubstProd with (D := D) ; auto.

      (* EqTySubstId *)
      - apply @EqTySubstId with (D := D) ; auto.

      (* EqTySubstEmpty *)
      - apply @EqTySubstEmpty with (D := D) ; auto.

      (* EqTySubstUnit *)
      - apply @EqTySubstUnit with (D := D) ; auto.

      (* EqTySubstBool *)
      - apply @EqTySubstBool with (D := D) ; auto.

      (* EqTyExfalso *)
      - apply @EqTyExfalso with (u := u) (H := H) ; auto.

      (* CongProd *)
      - apply CongProd ; auto.

      (* CongId *)
      - apply CongId ; auto.

      (* CongTySubst *)
      - apply @CongTySubst with (D := D) ; auto.

      (* CongSimProd *)
      - apply CongSimProd ; auto.

      (* EqTySubstSimProd *)
      - apply @EqTySubstSimProd with (D := D) ; auto.

      (* EqTySubstUni *)
      - apply @EqTySubstUni with (D := D) ; auto.

      (* ElProd *)
      - eapply ElProd ; eauto.

      (* ElProdProp *)
      - eapply ElProdProp ; eauto.

      (* ElId *)
      - eapply ElId ; eauto.

      (* ElSubst *)
      - eapply ElSubst ; eauto.

      (* ElEmpty *)
      - eapply ElEmpty ; eauto.

      (* ElUnit *)
      - eapply ElUnit ; eauto.

      (* ElBool *)
      - eapply ElBool ; eauto.

      (* ElSimProd *)
      - eapply ElSimProd ; eauto.

      (* ElSimProdProp *)
      - eapply ElSimProdProp ; eauto.

      (* ElUni *)
      - apply ElUni ; auto.

      (* ElProp *)
      - apply ElProp ; auto.

      (* CongEl *)
      - eapply CongEl ; eauto.
  }

  (* sane_eqterm *)
  - { destruct P ; doConfig.

      (* EqTyConv *)
      - apply @EqTyConv with (A := A) ; auto.

      (* EqCtxConv *)
      - apply @EqCtxConv with (G := G) ; auto.

      (* EqRefl *)
      - apply EqRefl ; auto.

      (* EqSym *)
      - apply EqSym ; auto.

      (* EqTrans *)
      - apply @EqTrans with (v := v) ; auto.

      (* EqIdSubst *)
      - apply EqIdSubst ; auto.

      (* EqSubstComp *)
      - apply @EqSubstComp with (D := D) (E := E) ; auto.

      (* EqSubstWeak *)
      - apply EqSubstWeak ; auto.


      (* EqSubstZeroZero *)
      - apply EqSubstZeroZero ; auto.

      (* EqSubstZeroSucc *)
      - apply EqSubstZeroSucc ; auto.

      (* EqSubstShiftZero *)
      - apply @EqSubstShiftZero with (D := D) ; auto.

      (* EqSubstShiftSucc *)
      - apply @EqSubstShiftSucc with (D := D) ; auto.

      (* EqSubstAbs *)
      - apply @EqSubstAbs with (D := D) ; auto.

      (* EqSubstApp *)
      - apply @EqSubstApp with (D := D) ; auto.

      (* EqSubstRefl *)
      - apply @EqSubstRefl with (D := D) ; auto.

      (* EqSubstJ *)
      - apply @EqSubstJ with (D := D) ; auto.

     (* This rule is subsumed by EqTermExfalso *)
      (* EqSubstExfalso *)
      - apply @EqSubstExfalso with (D := D) ; auto.

      (* EqSubstUnit *)
      - apply @EqSubstUnit with (D := D) ; auto.

      (* EqSubstTrue *)
      - apply @EqSubstTrue with (D := D) ; auto.

      (* EqSubstFalse *)
      - apply @EqSubstFalse with (D := D) ; auto.

      (* EqSubstCond *)
      - apply @EqSubstCond with (D := D) ; auto.

      (* EqTermExfalso *)
      - apply @EqTermExfalso with (w := w) (H := H) ; auto.

      (* UnitEta *)
      - apply UnitEta ; auto.

      (* EqReflection *)
      - apply @EqReflection with (p := p) ; auto.

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
      - apply @CongTermSubst with (D := D) ; auto.

      (* CongPair *)
      - apply CongPair ; auto.

      (* CongProjOne *)
      - apply CongProjOne ; auto.

      (* CongProjTwo *)
      - apply CongProjTwo ; auto.

      (* EqSubstPair *)
      - apply @EqSubstPair with (D := D) ; auto.

      (* EqSubstProjOne *)
      - apply @EqSubstProjOne with (D := D) ; auto.

      (* EqSubstProjTwo *)
      - apply @EqSubstProjTwo with (D := D) ; auto.

      (* ProjOnePair *)
      - apply ProjOnePair ; auto.

      (* ProjTwoPair *)
      - apply ProjTwoPair ; auto.

      (* PairEta *)
      - apply PairEta ; auto.

      (* EqSubstUniProd *)
      - apply @EqSubstUniProd with (D := D) ; auto.

      (* EqSubstUniProdProp *)
      - apply @EqSubstUniProdProp with (D := D) ; auto.

      (* EqSubstUniId *)
      - apply @EqSubstUniId with (D := D) ; auto.

      (* EqSubstUniEmpty *)
      - apply @EqSubstUniEmpty with (D := D) ; auto.

      (* EqSubstUniUnit *)
      - apply @EqSubstUniUnit with (D := D) ; auto.

      (* EqSubstUniBool *)
      - apply @EqSubstUniBool with (D := D) ; auto.

      (* EqSubstUniSimProd *)
      - apply @EqSubstUniSimProd with (D := D) ; auto.

      (* EqSubstUniSimProdProp *)
      - apply @EqSubstUniSimProdProp with (D := D) ; auto.

      (* EqSubstUniUni *)
      - apply @EqSubstUniUni with (D := D) ; auto.

      (* EqSubstUniProp *)
      - apply @EqSubstUniProp with (D := D) ; auto.

      (* CongUniProd *)
      - apply CongUniProd ; auto.

      (* CongUniProdProp *)
      - apply CongUniProdProp ; auto.

      (* CongUniId *)
      - apply CongUniId ; auto.

      (* CongUniSimProd *)
      - apply CongUniSimProd ; auto.

      (* CongUniSimProdProp *)
      - apply CongUniSimProdProp ; auto.
    }
Defined.

End Ptt2Ett.