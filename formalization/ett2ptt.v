Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require ett ptt ptt_sanity ptt_inversion.

Section Ett2Ptt.

Context `{configReflection : config.Reflection}.

(* Renaming ptt_sanity lemmata for readability. *)
Definition ptt_sane_issubst := ptt_sanity.sane_issubst.
Definition ptt_sane_istype  := ptt_sanity.sane_istype.
Definition ptt_sane_isterm  := ptt_sanity.sane_isterm.
Definition ptt_sane_eqctx   := ptt_sanity.sane_eqctx.
Definition ptt_sane_eqtype  := ptt_sanity.sane_eqtype.
Definition ptt_sane_eqsubst := ptt_sanity.sane_eqsubst.
Definition ptt_sane_eqterm  := ptt_sanity.sane_eqterm.

(* Same for inversion *)
Definition ptt_CtxExtendInversion := ptt_inversion.CtxExtendInversion.
Definition ptt_TyProdInversion    := ptt_inversion.TyProdInversion.
Definition ptt_TyIdInversion      := ptt_inversion.TyIdInversion.


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
         capply (@SubstComp _ _ G D E).
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
         capply (@SubstCtxConv _ _ G1 G2 D1 D2).
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
    { capply (@TyCtxConv _ _ G D).
      - now apply sane_istype.
      - now apply sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
    }

    (* TySubst *)
    { capply (@TySubst _ _ G D).
      - now apply sane_issubst.
      - now apply sane_istype.
      - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (ptt_sane_istype D A), sane_istype.
    }

    (* TyProd *)
    { capply TyProd.
      - now apply sane_istype.
      - now apply (ptt_CtxExtendInversion G A),
                  (ptt_sane_istype _ B), sane_istype.
      - now apply (ptt_CtxExtendInversion G A),
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
  }

  (****** sane_isterm ******)
  { destruct P.

    (* TermTyConv *)
    - { capply (@TermTyConv _ _ G A B).
        - now apply sane_isterm.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      }

    (* TermCtxConv *)
    - { capply (@TermCtxConv _ _ G D).
        - now apply sane_isterm.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
      }

    (* TermSubst *)
    - { capply (@TermSubst _ _ G D A).
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
        - now apply (ptt_CtxExtendInversion G A),
                    (ptt_sane_isterm _ u B), sane_isterm.
        - now apply (ptt_CtxExtendInversion G A),
                    (ptt_sane_isterm _ u B), sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend G A) u B), sane_isterm.
        - now apply sane_isterm.
      }

    (* TermApp *)
    - { capply TermApp.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (ptt_TyProdInversion G A B),
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
    - { capply (@CtxTrans _ _ G D E).
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
    - { capply (@SubstTrans _ _ G D sb1 sb2 sb3).
        - now apply sane_eqsubst.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb2 sb3 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
      }

    (* CongSubstZero *)
    - { capply (@CongSubstZero _ _ G).
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
    - { capply (@CongSubstComp _ _ G D E).
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
    - { capply (@EqSubstCtxConv _ _ G1 G2 D1 D2).
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
    - { capply (@CompAssoc _ _ G D E F).
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
    - { capply (@CompShift _ _ G D).
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
    { capply (@EqTyCtxConv _ _ G D).
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
    { capply (@EqTyTrans _ _ G A B C).
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
    { capply (@EqTySubstComp _ _ G D E).
      - now apply sane_istype.
      - now apply sane_issubst.
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbt D E), sane_issubst.
    }

    (* EqTySubstProd *)
    { capply (@EqTySubstProd _ _ G D).
      - now apply sane_issubst.
      - now apply (ptt_CtxExtendInversion D A),
            (ptt_sane_istype _ B), sane_istype.
      - now apply sane_istype.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstId *)
    { capply (@EqTySubstId _ _ G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_isterm D u A), sane_isterm.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstEmpty *)
    { capply (@EqTySubstEmpty _ _ G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstUnit *)
    { capply (@EqTySubstUnit _ _ G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstBool *)
    { capply (@EqTySubstBool _ _ G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTyExfalso *)
    { capply (@EqTyExfalso _ _ G A B u).
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
    { capply (@CongTySubst _ _ G D).
      - now apply sane_eqsubst.
      - now apply sane_eqtype.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      - now apply (@ptt_sane_eqtype D A B), sane_eqtype.
      - now apply (@ptt_sane_eqtype D A B), sane_eqtype.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
    }
  }

  (****** sane_eqterm ******)
  { destruct P.

    (* EqTyConv *)
    - { capply (@EqTyConv _ _ G A B).
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
    }

    (* EqCtxConv *)
    - { capply (@EqCtxConv _ _ G D).
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
    - { capply (@EqTrans _ _ G A u v w).
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
    - { capply (@EqSubstComp _ _ G D E A u sbs sbt).
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
    - { capply (@EqSubstShiftZero _ _ G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* EqSubstShiftSucc *)
    - { capply (@EqSubstShiftSucc _ _ G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D (var k) B), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* EqSubstAbs *)
    - { capply (@EqSubstAbs _ _ G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_CtxExtendInversion D A),
                    (ptt_sane_isterm _ u B),
                    sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend D A) u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstApp *)
    - { capply (@EqSubstApp _ _ G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D v A), sane_isterm.
        - now apply (ptt_TyProdInversion D A B),
                    (ptt_sane_isterm D u _),
                    sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstRefl *)
    - { capply (@EqSubstRefl _ _ G D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
      }

    (* EqSubstJ *)
    - { capply (@EqSubstJ _ _ G D).
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
    - { capply (@EqSubstExfalso _ _ G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstUnit *)
    - { capply (@EqSubstUnit _ _ G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* EqSubstTrue *)
    - { capply (@EqSubstTrue _ _ G D).
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstFalse *)
    - { capply (@EqSubstFalse _ _ G D).
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstCond *)
    - { capply (@EqSubstCond _ _ G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqTermExfalso *)
    - { capply (@EqTermExfalso _ _ G A u v w).
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
    - { config apply @EqReflection with (w1 := w1) (w2 := w2).
        - auto.
        - now apply (@ptt_sane_isterm G w1 (Id A u v)), sane_isterm.
        - now apply (ptt_TyIdInversion G A u v),
                    (ptt_sane_isterm G w1 (Id A u v)),
                    sane_isterm.
        - now apply (ptt_TyIdInversion G A u v),
                    (ptt_sane_isterm G w1 (Id A u v)),
                    sane_isterm.
        - now apply (ptt_TyIdInversion G A u v),
                    (ptt_sane_isterm G w1 (Id A u v)),
                    sane_isterm.
        - now apply sane_isterm.
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
        - now apply (@ptt_sane_isterm G u (Prod A B)), sane_isterm.
        - now apply (ptt_TyProdInversion G A B),
                    (ptt_sane_isterm G u (Prod A B)),
                    sane_isterm.
        - now apply (ptt_TyProdInversion G A B),
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
    - { capply (@CongTermSubst _ _ G D).
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
  }

Defined.

End Ett2Ptt.
