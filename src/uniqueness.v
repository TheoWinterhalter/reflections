(* Uniqueness of typing. *)

Require Import config.
Require Import config_tactics.
Require Import wfconfig.

Require Import tt.
Require ett ptt.
Require ptt2ett ett2ptt.
Require ptt_admissible.
Require ett_sanity ptt_sanity.
Require Import tactics config_tactics.

Section Uniqueness.

Context {ConfigSyntax : config.Syntax}.
Context {ConfigReflection : config.Reflection}.
Context {ConfigSimpleProducts : config.SimpleProducts}.
Context {ConfigProdEta : config.ProdEta}.
Context {ConfigUniverseLevels : config.UniverseLevels}.
Context {ConfigUniverses : config.Universes}.
Context {ConfigWithProp : config.WithProp}.
Context {ConfigWithJ : config.WithJ}.
Context {ConfigEmpty : config.WithEmpty}.
Context {ConfigUnit : config.WithUnit}.
Context {ConfigBool : config.WithBool}.
Context {ConfigPi : config.WithPi}.
Context {ConfigUniProd : config.UniProd}.
Context {ConfigUniId : config.UniId}.
Context {ConfigUniEmpty : config.UniEmpty}.
Context {ConfigUniUnit : config.UniUnit}.
Context {ConfigUniBool : config.UniBool}.
Context {ConfigUniSimProd : config.UniSimProd}.

(* For PTT *)
Definition hasPrecond : config.Precond
  := {| config.precondFlag := config.Yes |}.
Context {ConfigCtxExtendInversion :
           CtxExtendInversionClass (ConfigPrecond := hasPrecond)}.
Context {ConfigTyIdInversion :
           TyIdInversionClass (ConfigPrecond := hasPrecond)}.
Context {ConfigTyProdInversion :
           TyProdInversionClass (ConfigPrecond := hasPrecond)}.
Context {ConfigTySimProdInversion :
           TySimProdInversionClass (ConfigPrecond := hasPrecond)}.

(* For ETT *)
Definition noPrecond : config.Precond
  := {| config.precondFlag := config.No |}.
Context {ConfigEqCtxExtendInversion :
           EqCtxExtendInversionClass (ConfigPrecond := noPrecond)}.

Lemma substCtxConv' :
  forall G G' D sbs (E : ett.eqctx G' G),
    ett.issubst sbs G D -> ett.issubst sbs G' D.
Proof.
  intros G G' D sbs E H.
  ceapply SubstCtxConv.
  - eassumption.
  - now capply CtxSym.
  - capply CtxRefl.
    now apply (ett_sanity.sane_issubst sbs G D).
Defined.

(* Tactics for dealing with the conversion cases. *)

Ltac doTyConv unique_term' :=
  ceapply EqTyTrans ;
  [ eapply unique_term' ;
    [ ehyp
    | hyp ]
  | ceapply EqTyCtxConv ;
    [ ehyp
    | hyp ] ].

Ltac doCtxConv D' unique_term' :=
  eapply unique_term' ;
  [ ehyp
  | (config apply @CtxTrans with (D := D')) ; hyp ].

Ltac doSubstConv unique_subst' :=
  ceapply CtxTrans ; [
    eapply unique_subst' ; [
      ehyp
    | ceapply CtxTrans ; [
        ehyp
      | capply CtxSym ; hyp
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
  { destruct H1 ; doConfig ;
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
        config apply @EqTyTrans with (B := A).
        + capply EqTySym. hyp.
        + eapply (unique_term_ctx G u A) ; eassumption.
      }

    (* TermCtxConv *)
    - {
        ceapply EqTyCtxConv.
        - eapply unique_term_ctx'.
          + ehyp.
          + ehyp.
          + config apply @CtxTrans with (D := D).
            * hyp.
            * capply CtxSym. hyp.
        - hyp.
      }

    (* TermSubst *)
    - { inversion_clear H2' ; doConfig.
        - doTyConv unique_term'.
        - doCtxConv D' unique_term'.

        - ceapply CongTySubst.
          + ceapply SubstRefl. ehyp.
          + eapply (unique_term_ctx' _ u).
            * hyp.
            * ehyp.
            * { capply CtxSym.
                apply (@unique_subst' G _ sbs) with (G' := G).
                - hyp.
                - eapply substCtxConv'.
                  + ceapply CtxSym.
                    ehyp.
                  + hyp.
                - capply CtxRefl. hyp.
              }
      }

    (* TermVarZero *)
    - { inversion H2' ; doConfig.
        - doTyConv unique_term'.
        - doCtxConv D' unique_term'.

        - { assert (L : ett.eqctx (ctxextend G0 A0) (ctxextend G A)).
            - rewrite H. hyp.
            - destruct (eqctx_ctxextend _ _ _ _  L) as [E M].
              ceapply CongTySubst.
              + ceapply CongSubstWeak.
                capply EqTySym.
                ceapply EqTyCtxConv ; ehyp.
              + capply EqTySym.
                ceapply EqTyCtxConv ; ehyp.
          }
      }


    (* TermVarSucc *)
      - { inversion H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { assert (L : ett.eqctx (ctxextend G0 B0) (ctxextend G B)).
              - rewrite H. hyp.
              - destruct (eqctx_ctxextend _ _ _ _  L) as [E M].
                ceapply CongTySubst.
                + ceapply CongSubstWeak.
                  capply EqTySym.
                  ceapply EqTyCtxConv ; ehyp.
                + eapply (unique_term_ctx' _ (var k)).
                  * hyp.
                  * ehyp.
                  * hyp.
            }
        }

      (* TermAbs *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - capply EqTyRefl.
            + capply TyProd. hyp.
        }

      (* TermApp *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { ceapply CongTySubst.
              - ceapply CongSubstZero.
                + ceapply EqTyRefl. hyp.
                + ceapply EqRefl. hyp.
              - ceapply EqTyRefl. hyp.
            }
        }

      (* TermRefl *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - config apply EqTyRefl, TyId.
            + hyp.
            + hyp.
        }

      (* TermJ *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { ceapply CongTySubst.
              - ceapply CongSubstZero.
                + ceapply EqTyRefl.
                  capply TyId ; hyp.
                + ceapply EqRefl. hyp.
              - ceapply CongTySubst.
                + { ceapply EqSubstCtxConv.
                    - ceapply CongSubstShift.
                      + ceapply CongSubstZero.
                        * ceapply EqTyRefl. ehyp.
                        * ceapply EqRefl. hyp.
                      + ceapply CongId.
                        * { ceapply CongTySubst.
                            - ceapply CongSubstWeak.
                              ceapply EqTyRefl. hyp.
                            - ceapply EqTyRefl. hyp.
                          }
                        * { ceapply CongTermSubst.
                            - ceapply CongSubstWeak.
                              ceapply EqTyRefl. hyp.
                            - ceapply EqRefl. hyp.
                          }
                        * ceapply EqRefl. ceapply TermVarZero. hyp.
                    - ceapply EqCtxExtend.
                      + hyp.
                      + { ceapply EqTyTrans.
                          - ceapply EqTySubstId.
                            + ceapply SubstZero. hyp.
                            + ceapply TermSubst.
                              * ceapply SubstWeak. hyp.
                              * hyp.
                            + ceapply TermVarZero. hyp.
                          - ceapply CongId.
                            + ceapply EqTySym.
                              eapply ptt2ett.sane_eqtype.
                              eapply ptt_admissible.EqTyWeakZero ; hyp.
                            + eapply ptt2ett.sane_eqterm.
                              { eapply ptt_admissible.EqSubstWeakZero ; try hyp.
                                - eapply ett2ptt.sane_istype.
                                  ceapply TySubst.
                                  + ceapply SubstZero. hyp.
                                  + ceapply TySubst.
                                    * ceapply SubstWeak. hyp.
                                    * hyp.
                                - eapply ett2ptt.sane_isterm.
                                  ceapply TermTyConv.
                                  + ehyp.
                                  + eapply ptt2ett.sane_eqtype.
                                    eapply ptt_admissible.EqTyWeakZero ; hyp.
                              }
                            + { ceapply EqTyConv.
                                - ceapply EqSubstZeroZero. hyp.
                                - eapply ptt2ett.sane_eqtype.
                                  eapply ptt_admissible.EqTyWeakZero ; hyp.
                              }
                        }
                    - ceapply CtxRefl.
                      capply CtxExtend.
                      capply TyId.
                      + ceapply TermSubst.
                        * ceapply SubstWeak. hyp.
                        * hyp.
                      + ceapply TermVarZero. hyp.
                  }
                + ceapply EqTyRefl. hyp.
            }
        }

      (* TermExfalso *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              ceapply TyCtxConv.
              + ehyp.
              + hyp.
            }
        }

      (* TermUnit *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - (config apply EqTyRefl, TyUnit) ; hyp.
        }

      (* TermTrue *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - (config apply EqTyRefl, TyBool) ; hyp.
        }

      (* TermFalse *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - (config apply EqTyRefl, TyBool) ; hyp.
        }

      (* TermCond *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { ceapply CongTySubst.
              - ceapply CongSubstZero.
                + ceapply EqTyRefl. capply TyBool. hyp.
                + ceapply EqRefl. hyp.
              - ceapply EqTyRefl. hyp.
            }
        }

      (* TermPair *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TySimProd.
              - hyp.
              - hyp.
            }
        }

      (* TermProjOne *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              ceapply TyCtxConv.
              - ehyp.
              - hyp.
            }
        }

      (* TermProjTwo *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              ceapply TyCtxConv.
              - ehyp.
              - hyp.
            }
        }

      (* TermUniProd *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TyUni.
              hyp.
            }
        }

      (* TermUniProdProp *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TyUni.
              hyp.
            }
        }

      (* TermUniId *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TyUni.
              hyp.
            }
        }

      (* TermUniEmpty *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TyUni.
              hyp.
            }
        }

      (* TermUniUnit *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TyUni.
              hyp.
            }
        }

      (* TermUniBool *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TyUni.
              hyp.
            }
        }

      (* TermUniSimProd *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TyUni.
              hyp.
            }
        }

      (* TermUniSimProdProp *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TyUni.
              hyp.
            }
        }

      (* TermUniUni *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TyUni.
              hyp.
            }
        }

      (* TermUniProp *)
      - { inversion_clear H2' ; doConfig.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { capply EqTyRefl.
              capply TyUni.
              hyp.
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
       - capply EqCtxExtend.
         + hyp.
         + capply EqTyRefl. hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstWeak *)
   - { inversion H2'; doConfig.
       - rewrite <- H1 in H3'.
         destruct (eqctx_ctxextend G A G0 A).
         + hyp.
         + subst. hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstShift *)
   - { inversion H2'; doConfig.
       - rewrite <- H3 in H3'.
         destruct (eqctx_ctxextend G (Subst A sbs) G0 (Subst A sbs)).
         + hyp.
         + capply EqCtxExtend.
           * apply (@unique_subst G _ sbs) with (G'0 := G).
             -- hyp.
             -- pex. ceapply SubstCtxConv.
                ++ ehyp.
                ++ ceapply CtxSym. hyp.
                ++ capply CtxRefl. hyp.
             -- pex. capply CtxRefl. hyp.
           * capply EqTyRefl. hyp.
       - doSubstConv unique_subst'.
     }

   (* H1: SubstId *)
   - { inversion H2'; doConfig.
       - rewrite <- H1. hyp.
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
   - config eapply @CtxTrans with (D := D1).
     + ceapply CtxSym. hyp.
     + eapply unique_subst.
       * ehyp.
       * ehyp.
       * capply ett2ptt.sane_eqctx.
         (config eapply @CtxTrans with (D := G2)) ; hyp.

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
  - apply CtxRefl. hyps.
Defined.

End Uniqueness.
