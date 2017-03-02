Require Import syntax.

Require ett ptt ptt_sanity ptt_inversion.

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
  { destruct P.

    (* CtxEmpty *)
    - { apply ptt.CtxEmpty. }

    (* CtxExtend *)
    - {
        intros ; apply ptt.CtxExtend.
        + now apply (ptt_sane_istype G A), sane_istype.
        + now apply sane_istype.
      }
  }

  (****** sane_issubst ******)
  { destruct P.

    (* SubstZero *)
    - { apply ptt.SubstZero.
        + now apply sane_isterm.
        + eapply ptt_sane_isterm.
          eapply sane_isterm ; eassumption.
        + eapply ptt_sane_isterm.
          eapply sane_isterm ; eassumption.
      }

    (* SubstWeak *)
    - {
        apply ptt.SubstWeak.
        + now apply sane_istype.
        + eapply ptt_sane_istype.
          eapply sane_istype ; eassumption.
      }

    (* SubstShift. *)
    - {
        apply ptt.SubstShift.
        + now apply sane_issubst.
        + now apply sane_istype.
        + eapply (ptt_sane_issubst sbs G D).
          now apply sane_issubst.
        + eapply (ptt_sane_istype D A).
          now apply sane_istype.
      }

     (* SubstId *)
     - {
         apply ptt.SubstId.
         - now apply sane_isctx.
       }

     (* SubstComp *)
     - {
         apply (@ptt.SubstComp G D E).
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
         apply (@ptt.SubstCtxConv G1 G2 D1 D2).
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
    { apply (@ptt.TyCtxConv G D).
      - now apply sane_istype.
      - now apply sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
    }

    (* TySubst *)
    { apply (@ptt.TySubst G D).
      - now apply sane_issubst.
      - now apply sane_istype.
      - now apply (ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (ptt_sane_istype D A), sane_istype.
    }

    (* TyProd *)
    { apply ptt.TyProd.
      - now apply sane_istype.
      - now apply (ptt_CtxExtendInversion G A),
                  (ptt_sane_istype _ B), sane_istype.
      - now apply (ptt_CtxExtendInversion G A),
                  (ptt_sane_istype _ B), sane_istype.
    }

    (* TyId *)
    { apply ptt.TyId.
      - now apply (ptt_sane_isterm G u A), sane_isterm.
      - now apply (ptt_sane_isterm G u A), sane_isterm.
      - now apply sane_isterm.
      - now apply sane_isterm.
    }

    (* TyEmpty *)
    { apply ptt.TyEmpty.
      - now apply sane_isctx.
    }

    (* TyUnit *)
    { apply ptt.TyUnit.
      - now apply sane_isctx.
    }

    (* TyBool *)
    { apply ptt.TyBool.
      - now apply sane_isctx.
    }
  }

  (****** sane_isterm ******)
  { destruct P.

    (* TermTyConv *)
    - { apply (@ptt.TermTyConv G A B).
        - now apply sane_isterm.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
      }

    (* TermCtxConv *)
    - { apply (@ptt.TermCtxConv G D).
        - now apply sane_isterm.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
      }

    (* TermSubst *)
    - { apply (@ptt.TermSubst G D A).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
      }

    (* TermVarZero *)
    - { apply ptt.TermVarZero.
        - now apply (@ptt_sane_istype G A), sane_istype.
        - now apply sane_istype.
      }

    (* TermVarSucc *)
    - { apply ptt.TermVarSucc.
        - now apply (@ptt_sane_istype G B), sane_istype.
        - now apply (@ptt_sane_isterm G (var k)A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* TermAbs *)
    - { apply ptt.TermAbs.
        - now apply (ptt_CtxExtendInversion G A),
                    (ptt_sane_isterm _ u B), sane_isterm.
        - now apply (ptt_CtxExtendInversion G A),
                    (ptt_sane_isterm _ u B), sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend G A) u B), sane_isterm.
        - now apply sane_isterm.
      }

    (* TermApp *)
    - { apply ptt.TermApp.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (ptt_TyProdInversion G A B),
                    (ptt_sane_isterm G u (Prod A B)),
                    sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* TermRefl *)
    - { apply ptt.TermRefl.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* TermJ *)
    - { apply ptt.TermJ.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* TermExfalso *)
    - { apply ptt.TermExfalso.
        - now apply (@ptt_sane_istype G A), sane_istype.
        - now apply sane_istype.
        - now apply sane_isterm.
      }

    (* TermUnit *)
    - { apply ptt.TermUnit.
        - now apply sane_isctx.
      }

    (* TermTrue *)
    - { apply ptt.TermTrue.
        - now apply sane_isctx.
      }

    (* TermFalse *)
    - { apply ptt.TermFalse.
        - now apply sane_isctx.
      }

    (* TermCond *)
    - { apply ptt.TermCond.
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
    - { apply ptt.CtxRefl.
        - now apply sane_isctx.
      }

    (* CtxSym *)
    - { apply ptt.CtxSym.
        - now apply sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
      }

    (* CtxTrans *)
    - { apply (@ptt.CtxTrans G D E).
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx D E), sane_eqctx.
        - now apply sane_eqctx.
        - now apply sane_eqctx.
      }

    (* EqCtxEmpty *)
    - { apply ptt.EqCtxEmpty.
      }

    (* EqCtxExtend *)
    - { apply ptt.EqCtxExtend.
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
    - { apply ptt.SubstRefl.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* SubstSym *)
    - { apply ptt.SubstSym.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs sbt G D), sane_eqsubst.
      }

    (* SubstTrans *)
    - { apply (@ptt.SubstTrans G D sb1 sb2 sb3).
        - now apply sane_eqsubst.
        - now apply sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb2 sb3 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sb1 sb2 G D), sane_eqsubst.
      }

    (* CongSubstZero *)
    - { apply (@ptt.CongSubstZero G1 G2).
        - now apply sane_eqctx.
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqctx G1 G2), sane_eqctx.
        - now apply (@ptt_sane_eqctx G1 G2), sane_eqctx.
        - now apply (@ptt_sane_eqtype G1 A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G1 A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqterm G1 u1 u2 A1), sane_eqterm.
        - now apply (@ptt_sane_eqterm G1 u1 u2 A1), sane_eqterm.
      }

    (* CongSubstWeak *)
    - { apply ptt.CongSubstWeak.
        - now apply sane_eqctx.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqctx G1 G2), sane_eqctx.
        - now apply (@ptt_sane_eqctx G1 G2), sane_eqctx.
        - now apply (@ptt_sane_eqtype G1 A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype G1 A1 A2), sane_eqtype.
      }

    (* CongSubstShift *)
    - { apply ptt.CongSubstShift.
        - now apply sane_eqctx.
        - now apply sane_eqsubst.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqctx G1 G2), sane_eqctx.
        - now apply (@ptt_sane_eqctx G1 G2), sane_eqctx.
        - now apply (@ptt_sane_eqtype D A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype D A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqtype D A1 A2), sane_eqtype.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G1 D), sane_eqsubst.
        - now apply (@ptt_sane_eqsubst sbs1 sbs2 G1 D), sane_eqsubst.
      }

    (* CongSubstComp *)
    - { apply (@ptt.CongSubstComp G D E).
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
    - { apply (@ptt.EqSubstCtxConv G1 G2 D1 D2).
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
    - { apply (@ptt.CompAssoc G D E F).
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbr E F), sane_issubst.
        - now apply (@ptt_sane_issubst sbr E F), sane_issubst.
      }

    (* WeakNat *)
    - { apply ptt.WeakNat.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* WeakZero *)
    - { apply ptt.WeakZero.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* ShiftZero *)
    - { apply ptt.ShiftZero.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
      }

    (* CompShift *)
    - { apply ptt.CompShift.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_istype E A), sane_istype.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* CompIdRight *)
    - { apply ptt.CompIdRight.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* CompIdLeft *)
    - { apply ptt.CompIdLeft.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }
  }


  (****** sane_eqtype ******)
  { destruct P.

    (* EqTyCtxConv *)
    { apply (@ptt.EqTyCtxConv G D).
      - now apply sane_eqtype.
      - now apply sane_eqctx.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
      - now apply (ptt_sane_eqctx G D), sane_eqctx.
    }

    (* EqTyRefl *)
    { apply ptt.EqTyRefl.
      - now apply (ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
    }

    (* EqTySym *)
    { apply ptt.EqTySym.
      - now apply sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
    }

    (* EqTyTrans *)
    { apply (@ptt.EqTyTrans G A B C).
      - now apply sane_eqtype.
      - now apply sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G A B), sane_eqtype.
      - now apply (ptt_sane_eqtype G B C), sane_eqtype.
    }

    (* EqTyIdSubst *)
    { apply ptt.EqTyIdSubst.
      - now apply (ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
    }

    (* EqTySubstComp *)
    { apply (@ptt.EqTySubstComp G D E).
      - now apply sane_istype.
      - now apply sane_issubst.
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbt D E), sane_issubst.
    }

    (* EqTySubstProd *)
    { apply (@ptt.EqTySubstProd G D).
      - now apply sane_issubst.
      - now apply sane_istype.
      - now apply sane_istype.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstId *)
    { apply (@ptt.EqTySubstId G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_isterm D u A), sane_isterm.
      - now apply sane_isterm.
      - now apply sane_isterm.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstEmpty *)
    { apply (@ptt.EqTySubstEmpty G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstUnit *)
    { apply (@ptt.EqTySubstUnit G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTySubstBool *)
    { apply (@ptt.EqTySubstBool G D).
      - now apply sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
    }

    (* EqTyExfalso *)
    { apply (@ptt.EqTyExfalso G A B u).
      - now apply (@ptt_sane_istype G A), sane_istype.
      - now apply sane_istype.
      - now apply sane_istype.
      - now apply sane_isterm.
    }

    (* CongProd *)
    { apply ptt.CongProd.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
      - now apply (@ptt_sane_eqtype G A1 B1), sane_eqtype.
      - now apply (@ptt_sane_eqtype (ctxextend G A1) A2 B2), sane_eqtype.
      - now apply sane_eqtype.
      - now apply sane_eqtype.
    }

    (* CongId *)
    { apply ptt.CongId.
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
    { apply (@ptt.CongTySubst G D).
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
    - { apply (@ptt.EqTyConv G A B).
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqtype G A B), sane_eqtype.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
    }

    (* EqCtxConv *)
    - { apply (@ptt.EqCtxConv G D).
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqctx G D), sane_eqctx.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqctx.
      }

    (* EqRefl *)
    - { apply ptt.EqRefl.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSym *)
    - { apply ptt.EqSym.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v u A), sane_eqterm.
      }

    (* EqTrans *)
    - { apply (@ptt.EqTrans G A u v w).
        - now apply sane_eqterm.
        - now apply sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G u v A), sane_eqterm.
        - now apply (@ptt_sane_eqterm G v w A), sane_eqterm.
      }

    (* EqIdSubst *)
    - { apply ptt.EqIdSubst.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstComp *)
    - { apply (@ptt.EqSubstComp G D E A u sbs sbt).
        - now apply sane_isterm.
        - now apply sane_issubst.
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbt D E), sane_issubst.
        - now apply (@ptt_sane_isterm E u A), sane_isterm.
      }

    (* EqSubstWeak *)
    - { apply ptt.EqSubstWeak.
        - now apply (@ptt_sane_istype G B), sane_istype.
        - now apply (@ptt_sane_isterm G (var k) A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* EqSubstZeroZero *)
    - { apply ptt.EqSubstZeroZero.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply (@ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstZeroSucc *)
    - { apply ptt.EqSubstZeroSucc.
        - now apply (@ptt_sane_isterm G u B), sane_isterm.
        - now apply (@ptt_sane_isterm G (var k) A), sane_isterm.
        - now apply (@ptt_sane_isterm G u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqSubstShiftZero *)
    - { apply (@ptt.EqSubstShiftZero G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_istype.
      }

    (* EqSubstShiftSucc *)
    - { apply (@ptt.EqSubstShiftSucc G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D (var k) B), sane_isterm.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
      }

    (* EqSubstAbs *)
    - { apply (@ptt.EqSubstAbs G D).
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
    - { apply ptt.EqSubstApp.
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
    - { apply (@ptt.EqSubstRefl G D).
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_isterm D u A), sane_isterm.
      }

    (* EqSubstJ *)
    - { apply ptt.EqSubstJ.
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
    - { apply (@ptt.EqSubstExfalso G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_issubst.
      }

    (* EqSubstUnit *)
    - { apply (@ptt.EqSubstUnit G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
      }

    (* EqSubstTrue *)
    - { apply (@ptt.EqSubstTrue G D).
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstFalse *)
    - { apply (@ptt.EqSubstFalse G D).
        - now apply sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
      }

    (* EqSubstCond *)
    - { apply (@ptt.EqSubstCond G D).
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply (@ptt_sane_issubst sbs G D), sane_issubst.
        - now apply sane_issubst.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqTermExfalso *)
    - { apply (@ptt.EqTermExfalso G A u v w).
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* UnitEta *)
    - { apply ptt.UnitEta.
        - now apply (@ptt_sane_isterm G u Unit), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* EqReflection *)
    - { apply (@ptt.EqReflection G A u v w1 w2).
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
    - { apply ptt.ProdBeta.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm G v A), sane_isterm.
        - now apply (@ptt_sane_isterm (ctxextend G A) u B), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* CondTrue *)
    - { apply ptt.CondTrue.
        - now apply (@ptt_sane_isterm G v (Subst C (sbzero G Bool true))), sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* CondFalse *)
    - { apply ptt.CondFalse.
        - now apply (@ptt_sane_isterm G v (Subst C (sbzero G Bool true))), sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
        - now apply sane_isterm.
      }

    (* ProdEta *)
    - { apply ptt.ProdEta.
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
    - { apply ptt.JRefl.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply (ptt_sane_isterm G u A), sane_isterm.
        - now apply sane_isterm.
        - now apply sane_istype.
        - now apply sane_isterm.
      }

    (* CongAbs *)
    - { apply ptt.CongAbs.
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
    - { apply ptt.CongApp.
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
    - { apply ptt.CongRefl.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqtype G A1 A2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 A1), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
      }

    (* CongJ *)
    - { apply ptt.CongJ.
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
    - { apply ptt.CongCond.
        - now apply (ptt_sane_eqterm G v1 v2 (Subst C1 (sbzero G Bool true))), sane_eqterm.
        - now apply (ptt_sane_eqtype (ctxextend G Bool) C1 C2), sane_eqtype.
        - now apply (ptt_sane_eqtype (ctxextend G Bool) C1 C2), sane_eqtype.
        - now apply (ptt_sane_eqterm G u1 u2 Bool), sane_eqterm.
        - now apply (ptt_sane_eqterm G u1 u2 Bool), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 (Subst C1 (sbzero G Bool true))), sane_eqterm.
        - now apply (ptt_sane_eqterm G v1 v2 (Subst C1 (sbzero G Bool true))), sane_eqterm.
        - now apply (ptt_sane_eqterm G w1 w2 (Subst C1 (sbzero G Bool false))), sane_eqterm.
        - now apply (ptt_sane_eqterm G w1 w2 (Subst C1 (sbzero G Bool false))), sane_eqterm.
        - now apply sane_eqterm.
        - now apply sane_eqtype.
        - now apply sane_eqterm.
        - now apply sane_eqterm.
      }

    (* CongTermSubst *)
    - { apply (@ptt.CongTermSubst G D).
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
