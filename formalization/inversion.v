(* Inversion lemmata that come after proving sanity. *)
(* We prove them from PTT to ETT for simplicity. *)

Require Import syntax.
Require ptt.
Require ptt_admissible.
Require Import ett.
Require ptt2ett ett2ptt.
Require ett_sanity.
Require Import tactics.

Fixpoint TermAbsInversion {G A B u T}
         (H : ptt.isterm G (lam A B u) T) {struct H} :
  isctx G *
  istype G A *
  istype (ctxextend G A) B *
  isterm (ctxextend G A) u B *
  eqtype G (Prod A B) T.
Proof.
  inversion H.

  - { destruct (@TermAbsInversion _ _ _ _ _ H0) as [[[[? ?] ?] ?] ?].
      repeat split ; try assumption.
      eapply EqTyTrans ; [
        eassumption
      | hyp ..
      ].
    }

  - { destruct (@TermAbsInversion _ _ _ _ _ H0) as [[[[? ?] ?] ?] ?].
      assert (eqctx (ctxextend G0 A) (ctxextend G A)).
      { eapply EqCtxExtend ; try hyp.
        eapply EqTyRefl ; assumption.
      }
      repeat split.
      - hyp.
      - eapply TyCtxConv ; ehyp.
      - eapply TyCtxConv ; ehyp.
      - eapply TermCtxConv ; ehyp.
      - eapply EqTyCtxConv ; ehyp.
    }

  - { repeat split ; try hyp.
      apply EqTyRefl ; try hyp.
      apply TyProd ; hyp.
    }

Defined.

Fixpoint TermAppInversion {G A B u v T}
         (H : ptt.isterm G (app u A B v) T) {struct H} :
  isctx G *
  istype G A *
  istype (ctxextend G A) B *
  isterm G u (Prod A B) *
  isterm G v A *
  eqtype G (Subst B (sbzero v)) T.
Proof.
  inversion H.

  - { destruct (@TermAppInversion _ _ _ _ _ _ H0) as [[[[[? ?] ?] ?] ?] ?].
      repeat split ; try hyp.
      eapply EqTyTrans ; [
        ehyp
      | hyp ..
      ].
    }

  - { destruct (@TermAppInversion _ _ _ _ _ _ H0) as [[[[[? ?] ?] ?] ?] ?].
      assert (eqctx (ctxextend G0 A) (ctxextend G A)).
      { eapply EqCtxExtend ; try hyp.
        eapply EqTyRefl ; hyp.
      }
      repeat split.
      - hyp.
      - eapply TyCtxConv ; ehyp.
      - eapply TyCtxConv ; ehyp.
      - eapply TermCtxConv ; ehyp.
      - eapply TermCtxConv ; ehyp.
      - eapply EqTyCtxConv ; try ehyp.
    }

  - { repeat split ; try hyp.
      apply EqTyRefl ; try hyp.
      eapply TySubst ; try hyp.
      - eapply SubstZero ; ehyp.
      - hyp.
    }

Defined.

Fixpoint TermReflInversion {G A u T}
         (H : ptt.isterm G (refl A u) T) {struct H} :
  isctx G *
  istype G A *
  isterm G u A *
  eqtype G (Id A u u) T.
Proof.
  inversion H.

  - { destruct (@TermReflInversion _ _ _ _ H0) as [[[? ?] ?] ?].
      repeat split ; try hyp.
      eapply EqTyTrans ; [
        ehyp
      | hyp ..
      ].
    }

  - { destruct (@TermReflInversion _ _ _ _ H0) as [[[? ?] ?] ?].
      repeat split.
      - hyp.
      - eapply TyCtxConv ; ehyp.
      - eapply TermCtxConv ; ehyp.
      - eapply EqTyCtxConv ; ehyp.
    }

  - { repeat split ; try hyp.
      apply EqTyRefl ; try hyp.
      eapply TyId ; hyp.
    }

Defined.

Fixpoint TermJInversion {G A u C w v p T}
         (H : ptt.isterm G (j A u C w v p) T) {struct H} :
  isctx G *
  istype G A *
  isterm G u A *
  istype
    (ctxextend
       (ctxextend G A)
       (Id
          (Subst A sbweak)
          (subst u sbweak)
          (var 0)
       )
    )
    C *
  isterm G
             w
             (Subst
                (Subst
                   C
                   (sbshift (sbzero u))
                )
                (sbzero (refl A u))
             ) *
  isterm G v A *
  isterm G p (Id A u v) *
  eqtype G
             (Subst
                (Subst
                   C
                   (sbshift
                      (sbzero v)
                   )
                )
                (sbzero p)
             )
             T.
Proof.
  inversion H.

  - { destruct (@TermJInversion _ _ _ _ _ _ _ _ H0)
        as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
      repeat split ; try hyp.
      eapply EqTyTrans ; [
        ehyp
      | try hyp ..
      ].
    }

  - { destruct (@TermJInversion _ _ _ _ _ _ _ _ H0)
        as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
      assert (
          eqctx
            (ctxextend (ctxextend G0 A)
                       (Id (Subst A sbweak)
                           (subst u sbweak)
                           (var 0)))
            (ctxextend (ctxextend G A)
                       (Id (Subst A sbweak)
                           (subst u sbweak)
                           (var 0)))
      ).
      { eapply EqCtxExtend.
        - eapply EqCtxExtend ; try hyp.
          eapply EqTyRefl ; hyp.
        - eapply CongId.
          + eapply CongTySubst.
            * eapply CongSubstWeak ; try hyp.
            * eapply EqTyRefl ; hyp.
          + eapply CongTermSubst.
            * eapply CongSubstWeak ; try hyp.
            * eapply EqRefl ; hyp.
          + eapply EqRefl.
            eapply TermVarZero. hyp.
      }
      repeat split.
      - hyp.
      - eapply TyCtxConv ; ehyp.
      - eapply TermCtxConv ; ehyp.
      - eapply TyCtxConv ; ehyp.
      - eapply TermCtxConv ; try ehyp.
      - eapply TermCtxConv ; ehyp.
      - eapply TermCtxConv ; ehyp.
      - eapply EqTyCtxConv ; try ehyp.
    }

  - { repeat split ; try hyp.
      apply EqTyRefl ; try hyp.
      eapply TySubst.
      - eapply SubstZero. ehyp.
      - eapply TySubst.
        + eapply SubstCtxConv.
          * { eapply SubstShift.
              - eapply SubstZero. ehyp.
              - eapply TyId.
                + eapply TermSubst.
                  * eapply SubstWeak. hyp.
                  * shelve.
                + eapply TermVarZero. hyp.
            }
          * { apply EqCtxExtend.
              - apply CtxRefl. hyp.
              - eapply EqTyTrans ; [
                  eapply EqTySubstId ; try ehyp
                | ..
                ].
                + eapply SubstZero. ehyp.
                + eapply TermSubst.
                  * eapply SubstWeak. hyp.
                  * shelve.
                + eapply TermVarZero. hyp.
                + { eapply CongId.
                    - apply EqTySym.
                      eapply ptt2ett.sane_eqtype.
                      eapply ptt_admissible.EqTyWeakZero ; ehyp.
                    - eapply ptt2ett.sane_eqterm.
                      eapply ptt_admissible.EqSubstWeakZero ;
                        try hyp.
                      + eapply ett2ptt.sane_istype.
                        eapply TySubst.
                        * eapply SubstZero. ehyp.
                        * eapply TySubst ; try ehyp.
                          eapply SubstWeak. hyp.
                      + shelve.
                      + eapply ett2ptt.sane_isterm.
                        eapply TermTyConv ; try ehyp.
                        eapply ptt2ett.sane_eqtype.
                        eapply ptt_admissible.EqTyWeakZero ; ehyp.
                      + ehyp.
                    - eapply EqTyConv.
                      + eapply EqSubstZeroZero. ehyp.
                      + eapply ptt2ett.sane_eqtype.
                        eapply ptt_admissible.EqTyWeakZero ; ehyp.
                  }
            }
          * apply CtxRefl.
            apply ptt2ett.sane_isctx.
            apply (ptt_sanity.sane_istype _ C). hyp.
        + hyp.
    }

    Unshelve. all:hyp.
Defined.

Fixpoint TermExfalsoInversion {G A u T}
         (H : ptt.isterm G (exfalso A u) T) {struct H} :
  isctx G *
  istype G A *
  isterm G u Empty *
  eqtype G A T.
Proof.
  inversion H.

  - { destruct (@TermExfalsoInversion _ _ _ _ H0) as [[[? ?] ?] ?].
      repeat split ; try hyp.
      eapply EqTyTrans ; [
        ehyp
      | try hyp ..
      ].
    }

  - { destruct (@TermExfalsoInversion _ _ _ _ H0) as [[[? ?] ?] ?].
      repeat split.
      - hyp.
      - eapply TyCtxConv ; ehyp.
      - eapply TermCtxConv ; ehyp.
      - eapply EqTyCtxConv ; ehyp.
    }

  - { repeat split ; try hyp.
      apply EqTyRefl ; hyp.
    }

Defined.

Fixpoint TermCondInversion {G C u v w T}
         (H : ptt.isterm G (cond C u v w) T) {struct H} :
  isctx G *
  isterm G u Bool *
  istype (ctxextend G Bool) C *
  isterm G v (Subst C (sbzero true)) *
  isterm G w (Subst C (sbzero false)) *
  eqtype G (Subst C (sbzero u)) T.
Proof.
  inversion H.

  - { destruct (@TermCondInversion _ _ _ _ _ _ H0)
        as [[[[[? ?] ?] ?] ?] ?].
      repeat split ; try hyp.
      eapply EqTyTrans ; [
        ehyp
      | try hyp ..
      ].
    }

  - { destruct (@TermCondInversion _ _ _ _ _ _ H0)
        as [[[[[? ?] ?] ?] ?] ?].
      assert (eqctx (ctxextend G0 Bool) (ctxextend G Bool)).
      { apply EqCtxExtend ; try ehyp.
        apply EqTyRefl. ett_sane.
      }
      repeat split.
      - hyp.
      - eapply TermCtxConv ; ehyp.
      - eapply TyCtxConv ; ehyp.
      - eapply TermCtxConv ; try ehyp.
      - eapply TermCtxConv ; try ehyp.
      - eapply EqTyCtxConv ; try ehyp.
    }

  - { repeat split ; try hyp.
      apply EqTyRefl ; try hyp.
      eapply TySubst.
      - eapply SubstZero. ehyp.
      - hyp.
    }

Defined.