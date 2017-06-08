Require Import config.
Require Import config_tactics.

Require Import tt.
Require ett ptt ptt_sanity.
Require Import wfconfig.

Section Ett2Ptt.

  Open Scope type_scope.

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

(* We need inversion lemmata and we can't prove them since the syntax
   is not necessarilly inductive and thus not necessarilly injective.

   We want them for PTT.
*)
Local Instance hasPrecond : config.Precond
  := {| config.precondFlag := config.Yes |}.
Context {ConfigCtxExtendInversion : CtxExtendInversionClass}.
Context {ConfigTyIdInversion : TyIdInversionClass}.
Context {ConfigTyProdInversion : TyProdInversionClass}.
Context {ConfigTySimProdInversion : TySimProdInversionClass}.

(* Renaming ptt_sanity lemmata for readability. *)
Definition ptt_sane_issubst := ptt_sanity.sane_issubst.
Definition ptt_sane_istype  := ptt_sanity.sane_istype.
Definition ptt_sane_isterm  := ptt_sanity.sane_isterm.
Definition ptt_sane_eqctx   := ptt_sanity.sane_eqctx.
Definition ptt_sane_eqtype  := ptt_sanity.sane_eqtype.
Definition ptt_sane_eqsubst := ptt_sanity.sane_eqsubst.
Definition ptt_sane_eqterm  := ptt_sanity.sane_eqterm.


Fixpoint sane_isctx G (P : ett.isctx G) {struct P} : ptt.isctx G

with sane_issubst sbs G D (P : ett.issubst sbs G D) {struct P} : ptt.issubst sbs G D

with sane_istype G A (P : ett.istype G A) {struct P} : ptt.istype G A

with sane_isterm G u A (P : ett.isterm G u A) {struct P} : ptt.isterm G u A

with sane_eqctx G D (P : ett.eqctx G D) {struct P} : ptt.eqctx G D

with sane_eqsubst sbs sbt G D (P : ett.eqsubst sbs sbt G D) {struct P} : ptt.eqsubst sbs sbt G D

with sane_eqtype G A B (P : ett.eqtype G A B) {struct P} : ptt.eqtype G A B

with sane_eqterm G u v A (P : ett.eqterm G u v A) {struct P} : ptt.eqterm G u v A.

Proof.

  (****** sane_isctx ******)
  { destruct P ; doConfig.

    (* CtxEmpty *)
    - { capply CtxEmpty. }

    (* CtxExtend *)
    - {
        intros ; capply CtxExtend.
        + now apply (ptt_sane_istype G A), sane_istype.
        + now apply sane_istype.
      }
  }

  (****** sane_issubst ******)
  { destruct P ; doConfig.

    (* SubstZero *)
    - { capply SubstZero.
        + now apply sane_isterm.
        + eapply ptt_sane_isterm.
          eapply sane_isterm ; eassumption.
        + eapply ptt_sane_isterm.
          eapply sane_isterm ; eassumption.
      }

    (* SubstWeak *)
    - {
        capply SubstWeak.
        + now apply sane_istype.
        + eapply ptt_sane_istype.
          eapply sane_istype ; eassumption.
      }

    (* SubstShift. *)
    - {
        capply SubstShift.
        + now apply sane_issubst.
        + now apply sane_istype.
        + eapply (ptt_sane_issubst sbs G D).
          now apply sane_issubst.
        + eapply (ptt_sane_istype D A).
          now apply sane_istype.
      }

     (* SubstId *)
     - {
         capply SubstId.
         - now apply sane_isctx.
       }

     (* SubstComp *)
     - {
         config apply @SubstComp with (D := D).
         - now apply sane_issubst.
         - now apply sane_issubst.
         - apply (ptt_sane_issubst sbs G D).
           now apply sane_issubst.
         - apply (ptt_sane_issubst sbt D E).
           now apply sane_issubst.
         - apply (ptt_sane_issubst sbt D E).
           now apply sane_issubst.
       }

     (* SubstCtxConv *)
     - {
         config apply @SubstCtxConv with (G1 := G1) (D1 := D1).
         - now apply sane_issubst.
         - now apply sane_eqctx.
         - now apply sane_eqctx.
         - apply (ptt_sane_eqctx G1 G2).
           now apply sane_eqctx.
         - apply (ptt_sane_eqctx G1 G2).
           now apply sane_eqctx.
         - apply (ptt_sane_eqctx D1 D2).
           now apply sane_eqctx.
         - apply (ptt_sane_eqctx D1 D2).
           now apply sane_eqctx.
       }
  }

  (****** sane_istype ******)
  { destruct P.

    (* TyCtxConv *)
    { config apply @TyCtxConv with (G := G).
      - now apply sane_istype.
      - now apply sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
    }

    (* TySubst *)
    { config apply @TySubst with (D := D).
      - now apply sane_issubst.
      - now apply sane_istype.
      - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (ptt_sane_istype D A), sane_istype.
    }

    (* TyProd *)
    { capply TyProd.
      - now apply sane_istype.
      - cut (ptt.isctx G * ptt.istype G A) ; [ intro h ; apply h | .. ].
        now apply (CtxExtendInversion G A),
                  (ptt_sane_istype _ B), sane_istype.
      - now apply (CtxExtendInversion G A),
                  (ptt_sane_istype _ B), sane_istype.
    }

    (* TyId *)
    { capply TyId.
      - now apply (ptt_sane_isterm G u A), sane_isterm.
      - now apply (ptt_sane_isterm G u A), sane_isterm.
      - now apply sane_isterm.
      - now apply sane_isterm.
    }

    (* TyEmpty *)
    { capply TyEmpty.
      - now apply sane_isctx.
    }

    (* TyUnit *)
    { capply TyUnit.
      - now apply sane_isctx.
    }

    (* TyBool *)
    { capply TyBool.
      - now apply sane_isctx.
    }

    (* TySimProd *)
    { capply TySimProd.
      - now apply (ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
      - now apply sane_istype.
    }

    (* TyUni *)
    { capply TyUni.
      now apply sane_isctx.
    }

    (* TyEl *)
    { capply TyEl.
      - now apply sane_isterm.
      - now apply (ptt_sane_isterm G a (Uni l)), sane_isterm.
    }
  }

  (****** sane_isterm ******)
  { destruct P.

    (* TermTyConv *)
    - { config apply @TermTyConv with (A := A).
        - now apply sane_isterm.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      }

    (* TermCtxConv *)
    - { config apply @TermCtxConv with (G := G).
        - now apply sane_isterm.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
      }

    (* TermSubst *)
    - { config apply @TermSubst with (D := D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
      }

    (* TermVarZero *)
    - { capply TermVarZero.
        - now apply (@ptt_sane_istype G A), sane_istype.
        - now apply sane_istype.
      }

    (* TermVarSucc *)
    - { capply TermVarSucc.
        - now apply (@ptt_sane_istype G B), sane_istype.
        - now apply (@ptt_sane_isterm G (var k)A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* TermAbs *)
    - { capply TermAbs.
        - now apply (CtxExtendInversion G A),
                    (ptt_sane_isterm _ u B), sane_isterm.
        - now apply (CtxExtendInversion G A),
                    (ptt_sane_isterm _ u B), sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend G A) u B), sane_isterm.
        - now apply sane_isterm.
      }

    (* TermApp *)
    - { capply TermApp.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (TyProdInversion G A B),
                    (ptt_sane_isterm G u (Prod A B)),
                    sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* TermRefl *)
    - { capply TermRefl.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* TermJ *)
    - { capply TermJ.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* TermExfalso *)
    - { capply TermExfalso.
        - now apply (@ptt_sane_istype G A), sane_istype.
        - now apply sane_istype.
        - now apply sane_isterm.
      }

    (* TermUnit *)
    - { capply TermUnit.
        - now apply sane_isctx.
      }

    (* TermTrue *)
    - { capply TermTrue.
        - now apply sane_isctx.
      }

    (* TermFalse *)
    - { capply TermFalse.
        - now apply sane_isctx.
      }

    (* TermCond *)
    - { capply TermCond.
        - now apply (@ptt_sane_isterm G u Bool), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* TermPair *)
    - { capply TermPair.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G v B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* TermProjOne *)
    - { capply TermProjOne.
        - now apply (ptt_sane_isterm G p (SimProd A B)), sane_isterm.
        - now apply (TySimProdInversion G A B),
                    (ptt_sane_isterm G p (SimProd A B)),
                    sane_isterm.
        - now apply (TySimProdInversion G A B),
                    (ptt_sane_isterm G p (SimProd A B)),
                    sane_isterm.
        - now apply sane_isterm.
      }

    (* TermProjTwo *)
    - { capply TermProjTwo.
        - now apply (ptt_sane_isterm G p (SimProd A B)), sane_isterm.
        - now apply (TySimProdInversion G A B),
                    (ptt_sane_isterm G p (SimProd A B)),
                    sane_isterm.
        - now apply (TySimProdInversion G A B),
                    (ptt_sane_isterm G p (SimProd A B)),
                    sane_isterm.
        - now apply sane_isterm.
      }

    (* TermUniProd *)
    - { capply TermUniProd.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_isterm G a (Uni (uni n))), sane_isterm.
      }

    (* TermUniProdProp *)
    - { capply TermUniProdProp.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_isterm G a (Uni l)), sane_isterm.
      }

    (* TermUniId *)
    - { capply TermUniId.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_isterm G a (Uni n)), sane_isterm.
      }

    (* TermUniEmpty *)
    - { capply TermUniEmpty.
        now apply sane_isctx.
      }

    (* TermUniUnit *)
    - { capply TermUniUnit.
        now apply sane_isctx.
      }

    (* TermUniBool *)
    - { capply TermUniBool.
        now apply sane_isctx.
      }

    (* TermUniSimProd *)
    - { capply TermUniSimProd.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_isterm G a (Uni (uni n))), sane_isterm.
      }

    (* TermUniSimProdProp *)
    - { capply TermUniSimProdProp.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_isterm G a (Uni prop)), sane_isterm.
      }

    (* TermUniUni *)
    - { capply TermUniUni.
        now apply sane_isctx.
      }

    (* TermUniProp *)
    - { capply TermUniProp.
        now apply sane_isctx.
      }
  }

  (****** sane_eqctx ******)
  { destruct P.

    (* CtxRefl *)
    - { capply CtxRefl.
        - now apply sane_isctx.
      }

    (* CtxSym *)
    - { capply CtxSym.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
      }

    (* CtxTrans *)
    - { config apply @CtxTrans with (D := D).
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx D E), sane_eqctx.
        - now apply sane_eqctx.
        - now apply sane_eqctx.
      }

    (* EqCtxEmpty *)
    - { capply EqCtxEmpty.
      }

    (* EqCtxExtend *)
    - { capply EqCtxExtend.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply sane_eqctx.
        - now apply sane_eqtype.
      }
  }

  (****** sane_eqsubst ******)
  { destruct P.

    (* SubstRefl *)
    - { capply SubstRefl.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* SubstSym *)
    - { capply SubstSym.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      }

    (* SubstTrans *)
    - { config apply @SubstTrans with (sb2 := sb2).
        - now apply sane_eqsubst.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb2 sb3 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
      }

    (* CongSubstZero *)
    - { config apply @CongSubstZero with (G := G).
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
      }

    (* CongSubstWeak *)
    - { capply CongSubstWeak.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A1 A2), sane_eqtype.
      }

    (* CongSubstShift *)
    - { capply CongSubstShift.
        - now apply sane_eqsubst.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqtype D A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype D A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype D A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
      }

    (* CongSubstComp *)
    - { config apply @CongSubstComp with (D := D).
        - now apply sane_eqsubst.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbt1 sbt2 D E), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbt1 sbt2 D E), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbt1 sbt2 D E), sane_eqsubst.
      }

    (* EqSubstCtxConv *)
    - { config apply @EqSubstCtxConv with (G1 := G1) (D1 := D1).
        - now apply sane_eqsubst.
        - now apply sane_eqctx.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_eqctx G1 G2), sane_eqctx.
        - now apply (@ptt_sane_eqctx G1 G2), sane_eqctx.
        - now apply (@ptt_sane_eqctx D1 D2), sane_eqctx.
        - now apply (@ptt_sane_eqctx D1 D2), sane_eqctx.
        - now apply (@ptt_sane_eqsubst sbs sbt G1 D1), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G1 D1), sane_eqsubst.
      }

    (* CompAssoc *)
    - { config apply @CompAssoc with (D := D) (E := E).
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbr E F), sane_issubst.
        - now apply (@ptt_sane_issubst sbr E F), sane_issubst.
      }

    (* WeakNat *)
    - { capply WeakNat.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* WeakZero *)
    - { capply WeakZero.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* ShiftZero *)
    - { capply ShiftZero.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
      }

    (* CompShift *)
    - { config apply @CompShift with (D := D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_istype E A), sane_istype.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* CompIdRight *)
    - { capply CompIdRight.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* CompIdLeft *)
    - { capply CompIdLeft.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }
  }


  (****** sane_eqtype ******)
  { destruct P.

    (* EqTyCtxConv *)
    { config apply @EqTyCtxConv with (G := G).
      - now apply sane_eqtype.
      - now apply sane_eqctx.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
    }

    (* EqTyRefl *)
    { capply EqTyRefl.
      - now apply (ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
    }

    (* EqTySym *)
    { capply EqTySym.
      - now apply sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
    }

    (* EqTyTrans *)
    { config apply @EqTyTrans with (B := B).
      - now apply sane_eqtype.
      - now apply sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G B C), sane_eqtype.
    }

    (* EqTyIdSubst *)
    { capply EqTyIdSubst.
      - now apply (ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
    }

    (* EqTySubstComp *)
    { config apply @EqTySubstComp with (D := D) (E := E).
      - now apply sane_istype.
      - now apply sane_issubst.
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbt D E), sane_issubst.
    }

    (* EqTySubstProd *)
    { config apply @EqTySubstProd with (D := D).
      - now apply sane_issubst.
      - now apply (CtxExtendInversion D A),
            (ptt_sane_istype _ B), sane_istype.
      - now apply sane_istype.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstId *)
    { config apply @EqTySubstId with (D := D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_isterm D u A), sane_isterm.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstEmpty *)
    { config apply @EqTySubstEmpty with (D := D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstUnit *)
    { config apply @EqTySubstUnit with (D := D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstBool *)
    { config apply @EqTySubstBool with (D := D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTyExfalso *)
    { config apply @EqTyExfalso with (u := u) (H := H).
      - now apply (@ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
      - now apply sane_istype.
      - now apply sane_isterm.
    }

    (* CongProd *)
    { capply CongProd.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
      - now apply sane_eqtype.
      - now apply sane_eqtype.
    }

    (* CongId *)
    { capply CongId.
      - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (@ptt_sane_eqterm G u1 v1 A), sane_eqterm.
      - now apply (@ptt_sane_eqterm G u2 v2 A), sane_eqterm.
      - now apply (@ptt_sane_eqterm G u1 v1 A), sane_eqterm.
      - now apply (@ptt_sane_eqterm G u2 v2 A), sane_eqterm.
      - now apply sane_eqtype.
      - now apply sane_eqterm.
      - now apply sane_eqterm.
    }

    (* CongTySubst *)
    { config apply @CongTySubst with (D := D).
      - now apply sane_eqsubst.
      - now apply sane_eqtype.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      - now apply (@ptt_sane_eqtype D A B), sane_eqtype.
      - now apply (@ptt_sane_eqtype D A B), sane_eqtype.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
    }

    (* CongSimProd *)
    { capply CongSimProd.
      - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
      - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
      - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
      - now apply (ptt_sane_eqtype G B1 B2), sane_eqtype.
      - now apply (ptt_sane_eqtype G B1 B2), sane_eqtype.
      - now apply sane_eqtype.
      - now apply sane_eqtype.
    }

    (* EqTySubstSimProd *)
    { config apply @EqTySubstSimProd with (D := D).
      - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (ptt_sane_istype D A), sane_istype.
      - now apply sane_issubst.
      - now apply sane_istype.
      - now apply sane_istype.
    }

    (* EqTySubstUni *)
    { config apply @EqTySubstUni with (D := D).
      - now apply sane_issubst.
      - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* ElProd *)
    { config apply @ElProd.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply (ptt_sane_isterm G a (Uni (uni n))), sane_isterm.
    }

    (* ElProdProp *)
    { config apply @ElProdProp.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply (ptt_sane_isterm G a (Uni l)), sane_isterm.
    }

    (* ElId *)
    { config apply @ElId.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply (ptt_sane_isterm G a (Uni n)), sane_isterm.
    }

    (* ElSubst *)
    { config apply @ElSubst with (D := D) (n := n).
      - now apply sane_issubst.
      - now apply sane_isterm.
      - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* ElEmpty *)
    { capply ElEmpty.
      now apply sane_isctx.
    }

    (* ElUnit *)
    { capply ElUnit.
      now apply sane_isctx.
    }

    (* ElBool *)
    { capply ElBool.
      now apply sane_isctx.
    }

    (* ElSimProd *)
    { config apply @ElSimProd.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply (ptt_sane_isterm G a (Uni (uni n))), sane_isterm.
    }

    (* ElSimProdProp *)
    { config apply @ElSimProdProp.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply (ptt_sane_isterm G a (Uni prop)), sane_isterm.
    }

    (* ElUni *)
    { config apply @ElUni with (n := n).
      now apply sane_isctx.
    }

    (* ElProp *)
    { config apply @ElProp.
      now apply sane_isctx.
    }

    (* CongEl *)
    { config apply @CongEl with (n := n).
      - now apply sane_eqterm.
      - now apply (ptt_sane_eqterm G a b (Uni n)), sane_eqterm.
      - now apply (ptt_sane_eqterm G a b (Uni n)), sane_eqterm.
      - now apply (ptt_sane_eqterm G a b (Uni n)), sane_eqterm.
    }

  }

  (****** sane_eqterm ******)
  { destruct P.

    (* EqTyConv *)
    - { config apply @EqTyConv with (A := A).
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
    }

    (* EqCtxConv *)
    - { config apply @EqCtxConv with (G := G).
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqctx.
      }

    (* EqRefl *)
    - { capply EqRefl.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSym *)
    - { capply EqSym.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
      }

    (* EqTrans *)
    - { config apply @EqTrans with (v := v).
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v w A), sane_eqterm.
      }

    (* EqIdSubst *)
    - { capply EqIdSubst.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstComp *)
    - { config apply @EqSubstComp with (D := D) (E := E).
        - now apply sane_isterm.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbt D E), sane_issubst.
        - now apply (@ptt_sane_isterm E u A), sane_isterm.
      }

    (* EqSubstWeak *)
    - { capply EqSubstWeak.
        - now apply (@ptt_sane_istype G B), sane_istype.
        - now apply (@ptt_sane_isterm G (var k) A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* EqSubstZeroZero *)
    - { capply EqSubstZeroZero.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstZeroSucc *)
    - { capply EqSubstZeroSucc.
        - now apply (@ptt_sane_isterm G u B), sane_isterm.
        - now apply (@ptt_sane_isterm G (var k) A), sane_isterm.
        - now apply (@ptt_sane_isterm G u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstShiftZero *)
    - { config apply @EqSubstShiftZero with (D := D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* EqSubstShiftSucc *)
    - { config apply @EqSubstShiftSucc with (D := D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D (var k) B), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* EqSubstAbs *)
    - { config apply @EqSubstAbs with (D := D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (CtxExtendInversion D A),
                    (ptt_sane_isterm _ u B),
                    sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend D A) u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstApp *)
    - { config apply @EqSubstApp with (D := D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D v A), sane_isterm.
        - now apply (TyProdInversion D A B),
                    (ptt_sane_isterm D u _),
                    sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstRefl *)
    - { config apply @EqSubstRefl with (D := D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
      }

    (* EqSubstJ *)
    - { config apply @EqSubstJ with (D := D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D v A), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstExfalso *)
    - { config apply @EqSubstExfalso with (D := D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstUnit *)
    - { config apply @EqSubstUnit with (D := D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* EqSubstTrue *)
    - { config apply @EqSubstTrue with (D := D).
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstFalse *)
    - { config apply @EqSubstFalse with (D := D).
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstCond *)
    - { config apply @EqSubstCond with (D := D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqTermExfalso *)
    - { config apply @EqTermExfalso with (w := w) (H := H).
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* UnitEta *)
    - { capply UnitEta.
        - now apply (@ptt_sane_isterm G u Unit), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqReflection *)
    - { config apply @EqReflection with (p := p).
        - assumption.
        - now apply (@ptt_sane_isterm G p (Id A u v)), sane_isterm.
        - now apply (TyIdInversion G A u v),
                    (ptt_sane_isterm G p (Id A u v)),
                    sane_isterm.
        - now apply (TyIdInversion G A u v),
                    (ptt_sane_isterm G p (Id A u v)),
                    sane_isterm.
        - now apply (TyIdInversion G A u v),
                    (ptt_sane_isterm G p (Id A u v)),
                    sane_isterm.
        - now apply sane_isterm.
      }

    (* ProdBeta *)
    - { capply ProdBeta.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend G A) u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* CondTrue *)
    - { capply CondTrue.
        - now apply (@ptt_sane_isterm G v (Subst C (sbzero Bool true))), sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* CondFalse *)
    - { capply CondFalse.
        - now apply (@ptt_sane_isterm G v (Subst C (sbzero Bool true))), sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* ProdEta *)
    - { capply ProdEta.
        - assumption.
        - now apply (@ptt_sane_isterm G u (Prod A B)), sane_isterm.
        - now apply (TyProdInversion G A B),
                    (ptt_sane_isterm G u (Prod A B)),
                    sane_isterm.
        - now apply (TyProdInversion G A B),
                    (ptt_sane_isterm G u (Prod A B)),
                    sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_eqterm.
      }

    (* JRefl *)
    - { capply JRefl.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
      }

    (* CongAbs *)
    - { capply CongAbs.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
        - now apply (ptt_sane_eqterm (ctxextend G A1) u1 u2 A2), sane_eqterm.
        - now apply (ptt_sane_eqterm (ctxextend G A1) u1 u2 A2), sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqtype.
        - now apply sane_eqterm.
      }

    (* CongApp *)
    - { capply CongApp.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 B1), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 v1 (Prod A1 A2)), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 v1 (Prod A1 A2)), sane_eqterm.
        - now apply (ptt_sane_eqterm G u2 v2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G u2 v2 A1), sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
      }

    (* CongRefl *)
    - { capply CongRefl.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
      }

    (* CongJ *)
    - { capply CongJ.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype _ C1 C2), sane_eqtype.
        - now apply (ptt_sane_eqtype _ C1 C2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G p1 p2 _), sane_eqterm.
        - now apply (ptt_sane_eqterm G p1 p2 _), sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply (ptt_sane_eqterm G w1 w2 _), sane_eqterm.
        - now apply (ptt_sane_eqterm G w1 w2 _), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
      }

    (* CongCond *)
    - { capply CongCond.
        - now apply (ptt_sane_eqterm G v1 v2 (Subst C1 (sbzero Bool true))), sane_eqterm.
        - now apply (ptt_sane_eqtype (ctxextend G Bool) C1 C2), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G Bool) C1 C2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 Bool), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 Bool), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 (Subst C1 (sbzero Bool true))), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 (Subst C1 (sbzero Bool true))), sane_eqterm.
        - now apply (ptt_sane_eqterm G w1 w2 (Subst C1 (sbzero Bool false))), sane_eqterm.
        - now apply (ptt_sane_eqterm G w1 w2 (Subst C1 (sbzero Bool false))), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
      }

    (* CongTermSubst *)
    - { config apply @CongTermSubst with (D := D).
        - now apply sane_eqsubst.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqterm D u1 u2 A), sane_eqterm.
        - now apply (@ptt_sane_eqterm D u1 u2 A), sane_eqterm.
        - now apply (@ptt_sane_eqterm D u1 u2 A), sane_eqterm.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      }

    (* CongPair *)
    - { capply CongPair.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G B1 B2), sane_eqtype.
        - now apply (ptt_sane_eqtype G B1 B2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 B1), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 B1), sane_eqterm.
      }

    (* CongProjOne *)
    - { capply CongProjOne.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G B1 B2), sane_eqtype.
        - now apply (ptt_sane_eqtype G B1 B2), sane_eqtype.
        - now apply (ptt_sane_eqterm G p1 p2 (SimProd A1 B1)), sane_eqterm.
        - now apply (ptt_sane_eqterm G p1 p2 (SimProd A1 B1)), sane_eqterm.
      }

    (* CongProjTwo *)
    - { capply CongProjTwo.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G B1 B2), sane_eqtype.
        - now apply (ptt_sane_eqtype G B1 B2), sane_eqtype.
        - now apply (ptt_sane_eqterm G p1 p2 (SimProd A1 B1)), sane_eqterm.
        - now apply (ptt_sane_eqterm G p1 p2 (SimProd A1 B1)), sane_eqterm.
      }

    (* EqSubstPair *)
    - { (* The fact that D gets renamed to D0 is utterly stupid!
           This isn't a variable name...
         *)
        config apply EqSubstPair with (D0 := D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_isterm D u A), sane_isterm.
        - now apply (ptt_sane_isterm D v B), sane_isterm.
      }

    (* EqSubstProjOne *)
    - { config apply EqSubstProjOne with (D0 := D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (TySimProdInversion D A B),
                    (ptt_sane_isterm D p (SimProd A B)),
                    sane_isterm.
        - now apply (TySimProdInversion D A B),
                    (ptt_sane_isterm D p (SimProd A B)),
                    sane_isterm.
      }

    (* EqSubstProjTwo *)
    - { config apply EqSubstProjTwo with (D0 := D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (TySimProdInversion D A B),
                    (ptt_sane_isterm D p (SimProd A B)),
                    sane_isterm.
        - now apply (TySimProdInversion D A B),
                    (ptt_sane_isterm D p (SimProd A B)),
                    sane_isterm.
      }

    (* ProjOnePair *)
    - { capply ProjOnePair.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G v B), sane_isterm.
      }

    (* ProjTwoPair *)
    - { capply ProjTwoPair.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G v B), sane_isterm.
      }

    (* PairEta *)
    - { capply PairEta.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_eqterm G (proj1 A B p) (proj1 A B q) A),
                    sane_eqterm.
        - now apply (ptt_sane_eqterm G (proj1 A B p) (proj1 A B q) A),
                    sane_eqterm.
        - now apply (ptt_sane_eqterm G (proj2 A B p) (proj2 A B q) B),
                    sane_eqterm.
      }

    (* EqSubstUniProd *)
    - { config apply @EqSubstUniProd with (D := D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstUniProdProp *)
    - { config apply @EqSubstUniProdProp with (D := D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstUniId *)
    - { config apply @EqSubstUniId with (D := D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstUniEmpty *)
    - { config apply @EqSubstUniEmpty with (D := D).
        - now apply sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstUniUnit *)
    - { config apply @EqSubstUniUnit with (D := D).
        - now apply sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstUniBool *)
    - { config apply @EqSubstUniBool with (D := D).
        - now apply sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstUniSimProd *)
    - { config apply @EqSubstUniSimProd with (D := D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstUniSimProdProp *)
    - { config apply @EqSubstUniSimProdProp with (D := D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstUniUni *)
    - { config apply @EqSubstUniUni with (D := D).
        - now apply sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstUniProp *)
    - { config apply @EqSubstUniProp with (D := D).
        - now apply sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* CongUniProd *)
    - { capply CongUniProd.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni (uni n))), sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni (uni n))), sane_eqterm.
        - now apply (ptt_sane_eqterm (ctxextend G (El (uni n) a1))
                                     b1 b2 (Uni (uni m))),
                    sane_eqterm.
        - now apply (ptt_sane_eqterm (ctxextend G (El (uni n) a1)) b1 b2 (Uni (uni m))),
                    sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni (uni n))), sane_eqterm.
      }

    (* CongUniProdProp *)
    - { capply CongUniProdProp.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni l)), sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni l)), sane_eqterm.
        - now apply (ptt_sane_eqterm (ctxextend G (El l a1)) b1 b2 (Uni prop)),
                    sane_eqterm.
        - now apply (ptt_sane_eqterm (ctxextend G (El l a1)) b1 b2 (Uni prop)),
                    sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni l)), sane_eqterm.
      }

    (* CongUniId *)
    - { capply CongUniId.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni n)), sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni n)), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 (El n a1)), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 (El n a1)), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 (El n a1)), sane_eqterm.
        - ceapply TermTyConv.
          + now apply (ptt_sane_eqterm G v1 v2 (El n a1)), sane_eqterm.
          + config apply @CongEl with (n := n).
            * now apply sane_eqterm.
            * now apply (ptt_sane_eqterm G a1 a2 (Uni n)), sane_eqterm.
            * now apply (ptt_sane_eqterm G a1 a2 (Uni n)), sane_eqterm.
            * now apply (ptt_sane_eqterm G a1 a2 (Uni n)), sane_eqterm.
          + now apply (ptt_sane_eqterm G a1 a2 (Uni n)), sane_eqterm.
          + now apply (ptt_sane_eqterm G v1 v2 (El n a1)), sane_eqterm.
          + capply @TyEl.
            * now apply (ptt_sane_eqterm G a1 a2 (Uni n)), sane_eqterm.
            * now apply (ptt_sane_eqterm G a1 a2 (Uni n)), sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni n)), sane_eqterm.
      }

    (* CongUniSimProd *)
    - { capply CongUniSimProd.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni (uni n))), sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni (uni n))), sane_eqterm.
        - now apply (ptt_sane_eqterm G b1 b2 (Uni (uni m))), sane_eqterm.
        - now apply (ptt_sane_eqterm G b1 b2 (Uni (uni m))), sane_eqterm.
        - now apply (ptt_sane_eqterm G b1 b2 (Uni (uni m))), sane_eqterm.
      }

    (* CongUniSimProdProp *)
    - { capply CongUniSimProdProp.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni prop)), sane_eqterm.
        - now apply (ptt_sane_eqterm G a1 a2 (Uni prop)), sane_eqterm.
        - now apply (ptt_sane_eqterm G b1 b2 (Uni prop)), sane_eqterm.
        - now apply (ptt_sane_eqterm G b1 b2 (Uni prop)), sane_eqterm.
        - now apply (ptt_sane_eqterm G b1 b2 (Uni prop)), sane_eqterm.
      }
  }

Defined.

End Ett2Ptt.
