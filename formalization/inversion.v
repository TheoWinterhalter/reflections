(* Inversion lemmata that come after proving sanity. *)
(* We prove them from PTT to ETT for simplicity. *)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require ptt.
Require ptt_admissible.
Require ett.
Require ptt2ett ett2ptt.
Require ett_sanity.
Require Import tactics.

Section Inversion.

Context `{configReflection : config.Reflection}.

Fixpoint TermAbsInversion {G A B u T}
         (H : ptt.isterm G (lam A B u) T) {struct H} :
  ett.isctx G *
  ett.istype G A *
  ett.istype (ctxextend G A) B *
  ett.isterm (ctxextend G A) u B *
  ett.eqtype G (Prod A B) T.
Proof.
  inversion H ; doConfig.

    (* Type conversion *)
  - { destruct (@TermAbsInversion _ _ _ _ _ X) as [[[[? ?] ?] ?] ?].
      repeat split ; try assumption.
      ceapply EqTyTrans.
      - eassumption.
      - hyp.
    }

    (* Context conversion *)
  - { destruct (@TermAbsInversion _ _ _ _ _ X) as [[[[? ?] ?] ?] ?].
      assert (ett.eqctx (ctxextend G0 A) (ctxextend G A)).
      { ceapply EqCtxExtend ; try hyp.
        ceapply EqTyRefl ; assumption.
      }
      repeat split.
      - hyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply EqTyCtxConv ; ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; try hyp.
      capply TyProd ; hyp.
    }

Defined.

Fixpoint TermAppInversion {G A B u v T}
         (H : ptt.isterm G (app u A B v) T) {struct H} :
  ett.isctx G *
  ett.istype G A *
  ett.istype (ctxextend G A) B *
  ett.isterm G u (Prod A B) *
  ett.isterm G v A *
  ett.eqtype G (Subst B (sbzero A v)) T.
Proof.
  inversion H ; doConfig.

  - { destruct (@TermAppInversion _ _ _ _ _ _ X) as [[[[[? ?] ?] ?] ?] ?].
      repeat split ; try hyp.
      ceapply EqTyTrans ; [
        ehyp
      | hyp ..
      ].
    }

  - { destruct (@TermAppInversion _ _ _ _ _ _ X) as [[[[[? ?] ?] ?] ?] ?].
      assert (ett.eqctx (ctxextend G0 A) (ctxextend G A)).
      { ceapply EqCtxExtend ; try hyp.
        ceapply EqTyRefl ; hyp.
      }
      repeat split.
      - hyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply EqTyCtxConv ; try ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; try hyp.
      ceapply TySubst ; try hyp.
      - ceapply SubstZero ; ehyp.
      - hyp.
    }

Defined.

Fixpoint TermReflInversion {G A u T}
         (H : ptt.isterm G (refl A u) T) {struct H} :
  ett.isctx G *
  ett.istype G A *
  ett.isterm G u A *
  ett.eqtype G (Id A u u) T.
Proof.
  inversion H ; doConfig.

  - { destruct (@TermReflInversion _ _ _ _ X) as [[[? ?] ?] ?].
      repeat split ; try hyp.
      ceapply EqTyTrans ; [
        ehyp
      | hyp ..
      ].
    }

  - { destruct (@TermReflInversion _ _ _ _ X) as [[[? ?] ?] ?].
      repeat split.
      - hyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply EqTyCtxConv ; ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; try hyp.
      ceapply TyId ; hyp.
    }

Defined.

Fixpoint TermJInversion {G A u C w v p T}
         (H : ptt.isterm G (j A u C w v p) T) {struct H} :
  ett.isctx G *
  ett.istype G A *
  ett.isterm G u A *
  ett.istype
    (ctxextend
       (ctxextend G A)
       (Id
          (Subst A (sbweak A))
          (subst u (sbweak A))
          (var 0)
       )
    )
    C *
  ett.isterm G
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
             ) *
  ett.isterm G v A *
  ett.isterm G p (Id A u v) *
  ett.eqtype G
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
             T.
Proof.
  inversion H ; doConfig.

  - { destruct (@TermJInversion _ _ _ _ _ _ _ _ X)
        as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
      repeat split ; try hyp.
      ceapply EqTyTrans ; [
        ehyp
      | try hyp ..
      ].
    }

  - { destruct (@TermJInversion _ _ _ _ _ _ _ _ X)
        as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
      assert (
          ett.eqctx
            (ctxextend (ctxextend G0 A)
                       (Id (Subst A (sbweak A))
                           (subst u (sbweak A))
                           (var 0)))
            (ctxextend (ctxextend G A)
                       (Id (Subst A (sbweak A))
                           (subst u (sbweak A))
                           (var 0)))
      ).
      { ceapply EqCtxExtend.
        - ceapply EqCtxExtend ; try hyp.
          ceapply EqTyRefl ; hyp.
        - ceapply CongId.
          + ceapply CongTySubst.
            * ceapply CongSubstWeak ; try hyp.
              ceapply EqTyRefl ; hyp.
            * ceapply EqTyRefl ; hyp.
          + ceapply CongTermSubst.
            * ceapply CongSubstWeak ; try hyp.
              ceapply EqTyRefl ; hyp.
            * ceapply EqRefl ; hyp.
          + ceapply EqRefl.
            ceapply TermVarZero. hyp.
      }
      repeat split.
      - hyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; try ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply EqTyCtxConv ; try ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; try hyp.
      ceapply TySubst.
      - ceapply SubstZero. hyp.
      - ceapply TySubst.
        + ceapply SubstCtxConv.
          * { ceapply SubstShift.
              - ceapply SubstZero. ehyp.
              - ceapply TyId.
                + ceapply TermSubst.
                  * ceapply SubstWeak. hyp.
                  * hyp.
                + ceapply TermVarZero. hyp.
            }
          * { capply EqCtxExtend.
              - capply CtxRefl. hyp.
              - ceapply EqTyTrans ; [
                  ceapply EqTySubstId ; try ehyp
                | ..
                ].
                + ceapply SubstZero. hyp.
                + ceapply TermSubst.
                  * ceapply SubstWeak. hyp.
                  * hyp.
                + ceapply TermVarZero. hyp.
                + { ceapply CongId.
                    - capply EqTySym.
                      eapply ptt2ett.sane_eqtype.
                      eapply ptt_admissible.EqTyWeakZero ; hyp.
                    - eapply ptt2ett.sane_eqterm.
                      eapply ptt_admissible.EqSubstWeakZero ;
                        try hyp.
                      + eapply ett2ptt.sane_istype.
                        ceapply TySubst.
                        * ceapply SubstZero. hyp.
                        * ceapply TySubst ; try ehyp.
                          ceapply SubstWeak. hyp.
                      + eapply ett2ptt.sane_isterm.
                        ceapply TermTyConv ; try ehyp.
                        eapply ptt2ett.sane_eqtype.
                        eapply ptt_admissible.EqTyWeakZero ; hyp.
                    - ceapply EqTyConv.
                      + ceapply EqSubstZeroZero. hyp.
                      + eapply ptt2ett.sane_eqtype.
                        eapply ptt_admissible.EqTyWeakZero ; hyp.
                  }
            }
          * capply CtxRefl.
            apply ptt2ett.sane_isctx.
            apply (ptt_sanity.sane_istype _ C). hyp.
        + hyp.
    }

Defined.

Fixpoint TermExfalsoInversion {G A u T}
         (H : ptt.isterm G (exfalso A u) T) {struct H} :
  ett.isctx G *
  ett.istype G A *
  ett.isterm G u Empty *
  ett.eqtype G A T.
Proof.
  inversion H ; doConfig.

  - { destruct (@TermExfalsoInversion _ _ _ _ X) as [[[? ?] ?] ?].
      repeat split ; try hyp.
      ceapply EqTyTrans ; [
        ehyp
      | try hyp ..
      ].
    }

  - { destruct (@TermExfalsoInversion _ _ _ _ X) as [[[? ?] ?] ?].
      repeat split.
      - hyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply EqTyCtxConv ; ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; hyp.
    }

Defined.

Fixpoint TermCondInversion {G C u v w T}
         (H : ptt.isterm G (cond C u v w) T) {struct H} :
  ett.isctx G *
  ett.isterm G u Bool *
  ett.istype (ctxextend G Bool) C *
  ett.isterm G v (Subst C (sbzero Bool true)) *
  ett.isterm G w (Subst C (sbzero Bool false)) *
  ett.eqtype G (Subst C (sbzero Bool u)) T.
Proof.
  inversion H ; doConfig.

  - { destruct (@TermCondInversion _ _ _ _ _ _ X)
        as [[[[[? ?] ?] ?] ?] ?].
      repeat split ; try hyp.
      ceapply EqTyTrans ; [
        ehyp
      | try hyp ..
      ].
    }

  - { destruct (@TermCondInversion _ _ _ _ _ _ X)
        as [[[[[? ?] ?] ?] ?] ?].
      assert (ett.eqctx (ctxextend G0 Bool) (ctxextend G Bool)).
      { capply EqCtxExtend ; try ehyp.
        capply EqTyRefl. tt_sane.
      }
      repeat split.
      - hyp.
      - ceapply TermCtxConv ; ehyp.
      - ceapply TyCtxConv ; ehyp.
      - ceapply TermCtxConv ; try ehyp.
      - ceapply TermCtxConv ; try ehyp.
      - ceapply EqTyCtxConv ; try ehyp.
    }

  - { repeat split ; try hyp.
      capply EqTyRefl ; try hyp.
      ceapply TySubst.
      - ceapply SubstZero. hyp.
      - hyp.
    }

Defined.

End Inversion.
