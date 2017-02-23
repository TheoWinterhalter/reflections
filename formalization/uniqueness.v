(* Uniqueness of typing. *)

Require Import syntax.
Require ett ptt.
Require ptt2ett ett2ptt.
Require ptt_admissible.
Require ett_sanity ptt_sanity.
Require ptt_inversion.
Require Import tactics.

(* Auxiliary inversion lemmas. *)

Fixpoint eqctx_ctxextend_left G A D
         (H : ett.eqctx (ctxextend G A) D) {struct H} :
  { G' : context &
    { A' : type &
      (D = ctxextend G' A') * ett.eqctx G G' * ett.eqtype G A A'
    }
  }%type

with eqctx_ctxextend_right D G A
                           (H : ett.eqctx D (ctxextend G A)) {struct H} :
  { G' : context &
    { A' : type &
      (D = ctxextend G' A') * ett.eqctx G G' * ett.eqtype G A A'
    }
  }%type.
Proof.
  (**** left ****)
  - { inversion_clear H.

      (* CtxRefl *)
      - exists G, A. repeat split.
        + apply ett.CtxRefl.
          eapply ptt2ett.sane_isctx.
          apply (ptt_inversion.CtxExtendInversion G A).
          now eapply ett2ptt.sane_isctx.
        + apply ett.EqTyRefl.
          eapply ptt2ett.sane_istype.
          apply (ptt_inversion.CtxExtendInversion G A).
          now eapply ett2ptt.sane_isctx.

      (* CtxSym *)
      - destruct (eqctx_ctxextend_right _ _ _ H0) as [G' [A' [[eq HG] HA]]].
        exists G', A'. repeat split ; assumption.

      (* CtxTrans *)
      - destruct (eqctx_ctxextend_left _ _ _ H0) as [G' [A' [[eq HG] HA]]].
        subst.
        destruct (eqctx_ctxextend_left _ _ _ H1) as [G'' [A'' [[eq' HG'] HA']]].
        exists G'', A''. repeat split.
        + assumption.
        + eapply ett.CtxTrans ; eassumption.
        + eapply ett.EqTyTrans.
          * eassumption.
          * eapply ett.EqTyCtxConv ; try eassumption.
            apply ett.CtxSym ; assumption.

      (* EqCtxExtend *)
      - exists D0, B. repeat split ; assumption.

    }

  (**** right ****)
  - { inversion_clear H.

      (* CtxRefl *)
      - exists G, A. repeat split.
        + apply ett.CtxRefl.
          eapply ptt2ett.sane_isctx.
          apply (ptt_inversion.CtxExtendInversion G A).
          now eapply ett2ptt.sane_isctx.
        + apply ett.EqTyRefl.
          eapply ptt2ett.sane_istype.
          apply (ptt_inversion.CtxExtendInversion G A).
          now eapply ett2ptt.sane_isctx.

      (* CtxSym *)
      - destruct (eqctx_ctxextend_left _ _ _ H0) as [G' [A' [[eq HG] HA]]].
        exists G', A'. repeat split ; assumption.

      (* CtxTrans *)
      - destruct (eqctx_ctxextend_right _ _ _ H1) as [G' [A' [[eq HG] HA]]].
        subst.
        destruct (eqctx_ctxextend_right _ _ _ H0) as [G'' [A'' [[eq' HG'] HA']]].
        exists G'', A''. repeat split.
        + assumption.
        + eapply ett.CtxTrans ; eassumption.
        + eapply ett.EqTyTrans.
          * eassumption.
          * eapply ett.EqTyCtxConv ; try eassumption.
            apply ett.CtxSym ; assumption.

      (* EqCtxExtend *)
      - exists G0, A0. repeat split.
        + now apply ett.CtxSym.
        + apply ett.EqTySym.
          eapply ett.EqTyCtxConv ; eassumption.

    }

Defined.

Definition eqctx_ctxextend G A G' A'
         (H : ett.eqctx (ctxextend G A) (ctxextend G' A')) :
  (ett.eqctx G G' * ett.eqtype G A A')%type.
Proof.
  destruct (eqctx_ctxextend_left _ _ _ H) as [G'' [A'' [[eq HG] HA]]].
  inversion eq. subst.
  split ; assumption.
Defined.


(* It looks like we need to strengthen some inference
   rules, as follows: *)

Lemma substCtxConv' :
  forall G G' D sbs (E : ett.eqctx G' G),
    ett.issubst sbs G D -> ett.issubst sbs G' D.
Proof.
  intros G G' D sbs E H.
  eapply ett.SubstCtxConv.
  - eassumption.
  - now apply ett.CtxSym.
  - apply ett.CtxRefl.
    now apply (ett_sanity.sane_issubst sbs G D).
Defined.

(* Tactics for dealing with the conversion cases. *)

Ltac doTyConv unique_term' :=
  eapply ett.EqTyTrans ;
  [ eapply unique_term' ;
    [ ehyp
    | hyp ]
  | eapply ett.EqTyCtxConv ;
    [ ehyp
    | hyp ] ].

Ltac doCtxConv D' unique_term' :=
  eapply unique_term' ;
  [ ehyp
  | apply (@ett.CtxTrans _ D') ; hyp ].

Ltac doSubstConv unique_subst' :=
  eapply ett.CtxTrans ; [
    eapply unique_subst' ; [
      ehyp
    | eapply ett.CtxTrans ; [
        ehyp
      | apply ett.CtxSym ; hyp
      ]
    ]
  | hyp
  ].

(* The version of the theorem that allows variation of the context. *)

Fixpoint unique_term_ctx G u A (H1 : ptt.isterm G u A) {struct H1}:
  forall B D,
    ptt.isterm D u B ->
    ptt.eqctx D G ->
    ett.eqtype G A B

with unique_subst G D1 sbs (H1 : ptt.issubst sbs G D1) {struct H1}:
  forall G' D2 (H2 : ptt.issubst sbs G' D2) (H3 : ptt.eqctx G G'),
    ett.eqctx D1 D2.

Proof.
  (* unique_term *)
  { destruct H1 ;
    simple refine (fix unique_term'' B' D' H2' H3' {struct H2'} := _) ;
    pose (
      unique_term' B' D' H1 H2 :=
        unique_term'' B' D'
                      H1
                      (ett2ptt.sane_eqctx D' _ H2)
    ) ;
    pose (
      unique_term_ctx' G u A H1 B D H2 H3 :=
        unique_term_ctx G u A
                        H1
                        B D
                        (ett2ptt.sane_isterm D u B H2)
                        (ett2ptt.sane_eqctx D G H3)
    ) ;
    pose (
      unique_subst' G D1 sbs H1 G' D2 H2 H3 :=
        unique_subst G D1 sbs
                     H1
                     G' D2
                     (ett2ptt.sane_issubst sbs G' D2 H2)
                     (ett2ptt.sane_eqctx G G' H3)
    ).

    (* H1: TermTyConv *)
    - {
        apply (@ett.EqTyTrans G _ A B').
        + apply ett.EqTySym. hyp.
        + eapply (unique_term_ctx G u A) ; eassumption.
      }

    (* TermCtxConv *)
    - {
        eapply ett.EqTyCtxConv.
        - eapply unique_term_ctx'.
          + ehyp.
          + ehyp.
          + apply (@ett.CtxTrans _ D).
            * hyp.
            * apply ett.CtxSym. hyp.
        - hyp.
      }

    (* TermSubst *)
    - { inversion_clear H2'.
        - doTyConv unique_term'.
        - doCtxConv D' unique_term'.

        - eapply ett.CongTySubst.
          + eapply ett.SubstRefl. ehyp.
          + eapply (unique_term_ctx' _ u).
            * hyp.
            * ehyp.
            * { apply ett.CtxSym.
                apply (@unique_subst' G _ sbs) with (G' := G).
                - hyp.
                - eapply substCtxConv'.
                  + eapply ett.CtxSym.
                    ehyp.
                  + hyp.
                - apply ett.CtxRefl. hyp.
              }
      }

    (* TermVarZero *)
    - { inversion H2'.
        - doTyConv unique_term'.
        - doCtxConv D' unique_term'.

        - { assert (L : ett.eqctx (ctxextend G0 A0) (ctxextend G A)).
            - rewrite H1. hyp.
            - destruct (eqctx_ctxextend _ _ _ _  L) as [E M].
              eapply ett.CongTySubst.
              + eapply ett.CongSubstWeak.
                hyp.
              + apply ett.EqTySym.
                eapply ett.EqTyCtxConv ; ehyp.
          }
      }


    (* TermVarSucc *)
      - { inversion H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { assert (L : ett.eqctx (ctxextend G0 B0) (ctxextend G B)).
              - rewrite H4. hyp.
              - destruct (eqctx_ctxextend _ _ _ _  L) as [E M].
                eapply ett.CongTySubst.
                + eapply ett.CongSubstWeak.
                  hyp.
                + eapply (unique_term_ctx' _ (var k)).
                  * hyp.
                  * ehyp.
                  * hyp.
            }
        }

      (* TermAbs *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - apply ett.EqTyRefl.
            + apply ett.TyProd. hyp.
        }

      (* TermApp *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { eapply ett.CongTySubst.
              - eapply ett.CongSubstZero.
                eapply ett.EqRefl. ehyp.
              - eapply ett.EqTyRefl. hyp.
            }
        }

      (* TermRefl *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - apply ett.EqTyRefl, ett.TyId.
            + hyp.
            + hyp.
        }

      (* TermJ *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { eapply ett.CongTySubst.
              - eapply ett.CongSubstZero.
                eapply ett.EqRefl. ehyp.
              - eapply ett.CongTySubst.
                + { eapply ett.EqSubstCtxConv.
                    - eapply ett.CongSubstShift.
                      + eapply ett.SubstRefl.
                        eapply ett.SubstZero.
                        ehyp.
                      + eapply ett.TyId.
                        * eapply ett.TermSubst.
                          -- eapply ett.SubstWeak. hyp.
                          -- pex. exact H1.
                        * eapply ett.TermVarZero. hyp.
                    - eapply ett.EqCtxExtend.
                      + hyp.
                      + { eapply ett.EqTyTrans.
                          - eapply ett.EqTySubstId.
                            + eapply ett.SubstZero. ehyp.
                            + eapply ett.TermSubst.
                              * eapply ett.SubstWeak. hyp.
                              * hyp.
                            + eapply ett.TermVarZero. hyp.
                          - eapply ett.CongId.
                            + eapply ett.EqTySym.
                              eapply ptt2ett.sane_eqtype.
                              eapply ptt_admissible.EqTyWeakZero ; ehyp.
                            + eapply ptt2ett.sane_eqterm.
                              { eapply ptt_admissible.EqSubstWeakZero ; try hyp.
                                4:ehyp.
                                - eapply ett2ptt.sane_istype.
                                  eapply ett.TySubst.
                                  + eapply ett.SubstZero. ehyp.
                                  + eapply ett.TySubst.
                                    * eapply ett.SubstWeak. hyp.
                                    * hyp.
                                - hyp.
                                - eapply ett2ptt.sane_isterm.
                                  eapply ett.TermTyConv.
                                  + ehyp.
                                  + eapply ptt2ett.sane_eqtype.
                                    eapply ptt_admissible.EqTyWeakZero ; ehyp.
                              }
                            + { eapply ett.EqTyConv.
                                - eapply ett.EqSubstZeroZero. ehyp.
                                - eapply ptt2ett.sane_eqtype.
                                  eapply ptt_admissible.EqTyWeakZero ; ehyp.
                              }
                        }
                    - eapply ett.CtxRefl.
                      apply ett.CtxExtend.
                      apply ett.TyId.
                      + eapply ett.TermSubst.
                        * eapply ett.SubstWeak. hyp.
                        * hyp.
                      + eapply ett.TermVarZero. hyp.
                  }
                + eapply ett.EqTyRefl. hyp.
            }
        }

      (* TermExfalso *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { apply ett.EqTyRefl.
              eapply ett.TyCtxConv.
              + ehyp.
              + hyp.
            }
        }

      (* TermUnit *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - apply ett.EqTyRefl, ett.TyUnit ; hyp.
        }

      (* TermTrue *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - apply ett.EqTyRefl, ett.TyBool ; hyp.
        }

      (* TermFalse *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - apply ett.EqTyRefl, ett.TyBool ; hyp.
        }

      (* TermCond *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { eapply ett.CongTySubst.
              - eapply ett.CongSubstZero.
                eapply ett.EqRefl. ehyp.
              - eapply ett.EqTyRefl. hyp.
            }
        }
  }

 (* unique_subst *)
 { destruct H1 ;
   simple refine (fix unique_subst'' G' D2' H2' H3' {struct H2'} := _) ;
   pose (
     unique_subst' G' D2' H2' H3' :=
       unique_subst'' G' D2' H2'
                      (ett2ptt.sane_eqctx _ G' H3')
   ).

   (* H1: SubstZero *)
   - { inversion_clear H2'.
       - apply ett.EqCtxExtend.
         + hyp.
         + apply (unique_term_ctx G u A i A0 G' H).
           pex. apply ett.CtxSym. hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstWeak *)
   - { inversion H2'.
       - rewrite <- H2 in H3'.
         destruct (eqctx_ctxextend G A G0 A0).
         + hyp.
         + subst. hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstShift *)
   - { inversion H2'.
       - rewrite <- H5 in H3'.
         destruct (eqctx_ctxextend G (Subst A sbs) G0 (Subst A0 sbs)).
         + hyp.
         + apply ett.EqCtxExtend.
           * apply (@unique_subst G _ sbs) with (G'0 := G).
             -- hyp.
             -- pex. eapply ett.SubstCtxConv.
                ++ pex. exact H0.
                ++ apply ett.CtxSym. hyp.
                ++ apply ett.CtxRefl. hyp.
             -- apply ptt.CtxRefl. hyp.
           * (* Do we have any hope of ever concluding? *)
             (* A[σ] = A0[σ] could hold for many reasons, some of which may
                actually have different A and A0. *)
             fail.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstId *)
   - { inversion_clear H2'.
       - apply ett.CtxRefl. hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstComp *)
   - { inversion_clear H2'.
       - eapply (unique_subst _ _ _ H1_0).
         + ehyp.
         + eapply ett2ptt.sane_eqctx.
           eapply (unique_subst _ _ _ H1_).
           * ehyp.
           * hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstCtxConv *)
   - eapply @ett.CtxTrans with (D := D1).
     + eapply ett.CtxSym. hyp.
     + eapply unique_subst.
       * ehyp.
       * ehyp.
       * apply ett2ptt.sane_eqctx.
         eapply @ett.CtxTrans with (D := G2) ; hyp.

 }

Defined.

(* The main theorem as it will probably be used. *)
Corollary unique_term {G A B u} :
  ptt.isterm G u A ->
  ptt.isterm G u B ->
  ett.eqtype G A B.

Proof.
  intros H1 H2.
  eapply unique_term_ctx.
  - eassumption.
  - eassumption.
  - apply ptt.CtxRefl. hyps.
Defined.
