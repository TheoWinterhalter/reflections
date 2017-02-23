(* Sanity theorems for ptt. *)

Require Import syntax.
Require Import ptt.
Require Import ptt_tactics ptt_admissible.

Definition sane_issubst sbs G D :
  issubst sbs G D -> isctx G * isctx D.
Proof.
  intro H ; destruct H.

  (* SubstZero *)
  { split.

    - assumption.
    - now apply CtxExtend.
  }

  (* SubstWeak *)
  { split.

    - now apply CtxExtend.
    - assumption.
  }

  (* SubstShift *)
  { split.

    - apply CtxExtend.
      + assumption.
      + now apply (@TySubst G D).
    - now apply CtxExtend.
  }

  (* SubstId *)
  { split.
    - assumption.
    - assumption.
  }

  (* SubstComp *)
  { split.
    - assumption.
    - assumption.
  }

  (* SubstCtxConv *)
  { split.
    - assumption.
    - assumption.
  }
Defined.

Definition sane_istype G A :
  istype G A -> isctx G.
Proof.
  intro H; destruct H ; assumption.
Defined.

Definition sane_isterm' G u A :
  isterm G u A -> istype G A.
Proof.
  intro H ; destruct H.

  (* TermTyConv *)
  { assumption. }

  (* TermCtxConv *)
  { now apply (@TyCtxConv G D). }

  (* TermSubst *)
  { now apply (@TySubst G D A sbs). }

  (* TermVarZero *)
  { eapply TySubst.
    - now eapply SubstWeak.
    - assumption.
    - now apply (@CtxExtend G A).
    - eassumption.
  }

  (* TermVarSucc *)
  { apply (@TySubst (ctxextend G B) G).
    - now apply SubstWeak.
    - assumption.
    - now apply CtxExtend.
    - assumption.
  }

  (* TermAbs *)
  { now apply (@TyProd). }

  (* TermApp *)
  { apply (@TySubst G (ctxextend G A)).
    - now apply SubstZero.
    - assumption.
    - assumption.
    - now apply CtxExtend.
  }

  (* TermRefl *)
  { now apply TyId. }

  (* TermJ *)
  { magic.
    Unshelve. all:try magic.
    Unshelve. all:try magic.
    Unshelve. all:try strictmagic.
    (* Very unsatisfying!! *)
  }

  (* TermExfalso *)
  { assumption. }

  (* TermUnit *)
  { now apply TyUnit. }

  (* TermTrue *)
  { now apply TyBool. }

  (* TermFalse *)
  { now apply TyBool. }

  (* TermCond *)
  { eapply (@TySubst G (ctxextend G Bool)).
    + apply SubstZero.
      * assumption.
      * now apply TyBool.
      * assumption.
    + assumption.
    + assumption.
    + apply CtxExtend.
      * assumption.
      * now apply TyBool.
  }
Defined.


Definition sane_isterm G u A :
  isterm G u A -> isctx G * istype G A.
Proof.
  intro H.
  pose (K := sane_isterm' G u A H).
  split ; [now apply (@sane_istype G A) | assumption].
Defined.

Definition sane_eqtype' G A B :
  eqtype G A B -> istype G A * istype G B.
Proof.
  intro H ; destruct H.

  (* EqTyCtxConv *)
  { split.
    - { now apply (@TyCtxConv G D). }
    - { now apply (@TyCtxConv G D). }
  }

  (* EqTyRefl*)
  { split ; assumption. }

  (* EqTySym *)
  { split ; assumption. }

  (* EqTyTrans *)
  { split ; assumption. }

  (* EqTyIdSubst *)
  { split.
    - eapply TySubst.
      + now apply SubstId.
      + assumption.
      + assumption.
      + eassumption.
    - assumption.
  }

  (* EqTySubstComp *)
  { split.
    - apply (@TySubst G D) ; auto.
      apply (@TySubst D E) ; auto.
    - apply (@TySubst G E) ; auto.
      apply (@SubstComp G D E) ; auto.
  }

  (* EqTySubstProd *)
  { split.
    - { apply (@TySubst G D) ; auto using TyProd. }
    - { apply TyProd ; auto.
        + apply (@TySubst _ (ctxextend D A)) ; auto.
          * now apply SubstShift.
          * apply CtxExtend ; auto.
            now apply (@TySubst G D).
          * now apply CtxExtend.
        + now apply (@TySubst G D).
      }
  }

  (* EqTySubstId *)
  { split.
    - { apply (@TySubst G D) ; auto using TyId. }
    - { apply TyId ; auto using (@TySubst G D), (@TermSubst G D). }
  }

  (* EqTySubstEmpty *)
  { split.
    - { apply (@TySubst G D) ; auto using TyEmpty. }
    - { now apply TyEmpty. }
  }

  (* EqTySubstUnit *)
  { split.
    - { apply (@TySubst G D) ; auto using TyUnit. }
    - { now apply TyUnit. }
  }

  (* EqTySubstBool *)
  { split.
    - { apply (@TySubst G D) ; auto using TyBool. }
    - { now apply TyBool. }
  }

  (* EqTyExfalso *)
  { split ; assumption. }

  (* CongProd *)
  { split.
    - { now apply TyProd. }
    - { apply TyProd ; auto.
        apply (@TyCtxConv (ctxextend G A1)) ; auto using CtxExtend.
        apply EqCtxExtend ; auto using CtxRefl.
      }
  }

  (* CongId *)
  { split.
    - { now apply TyId. }
    - { apply TyId.
        - assumption.
        - assumption.
        - now apply (@TermTyConv G A B v1).
        - now apply (@TermTyConv G A B v2).
      }
  }

  (* CongTySubst *)
  { split.
    - { now apply (@TySubst G D). }
    - { now apply (@TySubst G D). }
  }

Defined.

Theorem sane_eqctx G D :
  eqctx G D -> isctx G * isctx D.
Proof.
  intro H ; destruct H.

  (* CtxRefl *)
  { split.
    - assumption.
    - assumption.
  }

  (* CtxSym *)
  { split.
    - assumption.
    - assumption.
  }

  (* CtxTrans *)
  { split.
    - assumption.
    - assumption.
  }

  (* EqCtxEmpty *)
  { split.
    - now apply CtxEmpty.
    - now apply CtxEmpty.
  }

  (* EqCtxExtend *)
  { split.
    - now apply CtxExtend.
    - apply CtxExtend.
      + assumption.
      + apply (@TyCtxConv G D) ; auto.
  }

Defined.


Theorem sane_eqtype G A B :
  eqtype G A B -> isctx G * istype G A * istype G B.
Proof.
  intro H.
  destruct (sane_eqtype' G A B H).
  auto using (sane_istype G A).
Defined.

Theorem sane_eqsubst' sbs sbt G D :
  eqsubst sbs sbt G D -> issubst sbs G D * issubst sbt G D.
Proof.
  intro H ; destruct H.

  (* SubstRefl *)
  - { split.
      - assumption.
      - assumption.
    }

  (* SubstSym *)
  - { split.
      - assumption.
      - assumption.
    }

  (* SubstTrans *)
  - { split.
      - assumption.
      - assumption.
    }

  (* CongSubstZero *)
  - { split.
      - magic.
      - magic.
    }

  (* CongSubstWeak *)
  - { split.
      - magic.
      - magic.
    }

  (* CongSubstShift *)
  - { split.
      - magic.
      - eapply SubstCtxConv ; magic.
        Unshelve. all:strictmagic.
    }

  (* CongSubstComp *)
  - { split.
      - now apply (@SubstComp G D E).
      - now apply (@SubstComp G D E).
    }

  (* EqSubstCtxConv *)
  - { split.
      - now apply (@SubstCtxConv G1 G2 D1 D2).
      - now apply (@SubstCtxConv G1 G2 D1 D2).
    }

  (* CompAssoc *)
  - { split.
      - apply (@SubstComp G E F) ; auto.
        now apply (@SubstComp G D E).
      - apply (@SubstComp G D F); auto.
        now apply (@SubstComp D E F).
    }

  (* WeakNat *)
  - { split.
      - apply (@SubstComp _ (ctxextend D A)) ;
          auto using CtxExtend, (@TySubst G D), SubstShift, SubstWeak.
      - apply (@SubstComp _ G) ;
          auto using CtxExtend, (@TySubst G D), SubstWeak.
    }

  (* WeakZero *)
  - { split.
      - apply (@SubstComp _ (ctxextend G A)) ;
          auto using CtxExtend, SubstZero, SubstWeak.
      - now apply SubstId.
    }

  (* ShiftZero *)
  - { split.
      - apply (@SubstComp _ (ctxextend G (Subst A sbs))) ;
          auto using CtxExtend, (@TySubst G D), SubstZero, (@TermSubst G D), SubstShift.
      - apply (@SubstComp _ D) ;
          auto using CtxExtend, SubstZero.
    }

  (* CompShift *)
  - { split.
      - apply (@SubstComp _ (ctxextend D (Subst A sbt))) ;
          auto using CtxExtend, (@TySubst D E), SubstShift.
        + { apply (@SubstCtxConv (ctxextend G (Subst (Subst A sbt) sbs)) _
                                 (ctxextend D (Subst A sbt))) ;
            auto using CtxExtend, (@TySubst D E), (@TySubst G D), (@TySubst G E),
                       (@SubstComp G D E), SubstShift, CtxRefl.
            apply EqCtxExtend ;
                auto using CtxRefl, (@TySubst G D), (@TySubst D E),
                           (@TySubst G E), (@SubstComp G D E).
              now apply (@EqTySubstComp G D E).
          }
        + apply CtxExtend ; auto.
          apply (@TySubst G E) ; auto using (@SubstComp G D E).
      - apply SubstShift ; auto using (@SubstComp G D E).
    }

  (* CompIdRight *)
  - { split.
      - apply (@SubstComp G G D) ; auto using SubstId.
      - assumption.
    }

  (* CompIdLeft *)
  - { split.
      - apply (@SubstComp G D D) ; auto using SubstId.
      - assumption.
    }
Defined.

Theorem sane_eqsubst sbs sbt G D :
  eqsubst sbs sbt G D -> isctx G * isctx D * issubst sbs G D * issubst sbt G D.
Proof.
  intro H.
  destruct (sane_eqsubst' sbs sbt G D H).
  auto using (sane_issubst sbs G D).
Defined.

Theorem sane_eqterm' G u v A :
  eqterm G u v A -> isterm G u A * isterm G v A.
Proof.
  intro H ; destruct H.

  (* EqTyConv *)
  - { split.
      - { now apply (@TermTyConv G A B u). }
      - { now apply (@TermTyConv G A B v). }
    }

  (* EqCtxConv *)
  - { split.
      - { now apply (@TermCtxConv G D A). }
      - { now apply (@TermCtxConv G D A). }
    }

  (* EqRefl *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* EqSym *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* EqTrans *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* EqIdSubst *)
  - { split.
      - { apply (@TermTyConv G (Subst A (sbid' G)) A).
          - apply (@TermSubst G G) ; auto using SubstId.
          - now apply EqTyIdSubst.
          - assumption.
          - apply (@TySubst G G) ; auto using SubstId.
          - assumption.
        }
      - { assumption. }
    }

  (* EqSubstComp *)
  - { split.
      - { apply (@TermTyConv G (Subst (Subst A sbt) sbs) (Subst A (sbcomp sbt sbs))).
          - apply (@TermSubst G D) ; auto.
            + now apply (@TermSubst D E).
            + now apply (@TySubst D E).
          - now apply (@EqTySubstComp G D E).
          - assumption.
          - apply (@TySubst G D) ; auto.
            now apply (@TySubst D E).
          - apply (@TySubst G E) ; auto.
            now apply (@SubstComp G D E).
        }
      - { apply (@TermSubst G E) ; auto.
          now apply (@SubstComp G D E).
        }
    }

  (* EqSubstWeak *)
  - { split.
      - { apply (@TermSubst _ G) ; auto using CtxExtend.
          now apply SubstWeak.
        }
      - { now apply TermVarSucc. }
    }


  (* EqSubstZeroZero *)
  - { split.
      - { magic.
          Unshelve. all:strictmagic.
        }
      - { assumption. }
    }

  (* EqSubstZeroSucc *)
  - { split.
      - { magic.
          Unshelve. all:strictmagic.
        }
      - { assumption. }
    }

  (* EqSubstShiftZero *)
  - { split.
      - { magic.
          Unshelve. all:strictmagic.
        }
      - { magic. }
    }

  (* EqSubstShiftSucc *)
  - { split.
      - { magic.
          Unshelve. all:strictmagic.
        }
      - { magic. }
    }

  (* EqSubstAbs *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstApp *)
  - { split.
      - { magic. }
      - { magic.
          Unshelve. all:strictmagic.
        }
    }

  (* EqSubstRefl *)
  - { split.
      - { magic.
          Unshelve. all:strictmagic.
        }
      - { magic. }
    }

  (* EqSubstJ *)
  - { split.
      - { magic.
          Unshelve. all:try magic.
          Unshelve. all:magic.
          Unshelve. all:strictmagic.
          (* Again, I don't like it but well... *)
        }
      - { eapply TermTyConv ; [
            idtac
          | eapply EqTySym ; [
              eapply JTyConv
            | ..
            ]
          | ..
          ].
          - eapply TermTyConv.
            + eapply TermJ.
              * magic.
              * magic.
              * magic.
              * eapply TySubst.
                -- eapply SubstCtxConv ; [
                     eapply SubstShift
                   | ..
                   ].
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ eapply EqCtxExtend.
                      ** magic.
                      ** magic.
                      ** magic.
                      ** magic.
                      ** magic.
                      ** eapply @EqTyTrans
                         with (B := Subst (Id (Subst A sbweak)
                                             (subst u sbweak)
                                             (var 0))
                                         (sbshift sbs)) ; [
                           eapply EqTyRefl
                         | ..
                         ] ; magic.
                   ++ eapply CtxRefl ; magic.
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ magic.
                -- magic.
                -- magic.
                -- magic.
              * eapply TermTyConv ; [
                  eapply TermSubst ; [ eassumption | .. ]
                | ..
                ].
                -- magic.
                -- magic.
                -- magic.
                -- magic.
                -- eapply EqTyTrans ; [
                     eapply JTyConv
                   | ..
                   ].
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ magic.
                   ++ eapply CongTySubst ; [
                        idtac
                      | eapply EqTyRefl ; magic
                      | ..
                      ] ; magic.
                   ++ magic.
                   ++ magic.
                   ++ eapply TySubst.
                      ** magic.
                      ** eapply TySubst ; [
                           idtac
                         | eapply TySubst ; magic
                         | ..
                         ].
                         --- eapply SubstCtxConv ; [
                               eapply SubstShift
                             | ..
                             ].
                             +++ magic.
                             +++ magic.
                             +++ magic.
                             +++ magic.
                             +++ eapply EqCtxExtend.
                                 *** magic.
                                 *** magic.
                                 *** magic.
                                 *** magic.
                                 *** magic.
                                 *** eapply @EqTyTrans
                                     with (B := Subst (Id (Subst (Subst A sbs)
                                                                sbweak)
                                                         (subst (subst u sbs)
                                                                sbweak)
                                                         (var 0))
                                                     (sbzero (subst u sbs))) ; [
                                       eapply EqTyRefl
                                     | ..
                                     ] ; magic.
                             +++ magic.
                             +++ magic.
                             +++ magic.
                             +++ magic.
                             +++ magic.
                         --- magic.
                         --- magic.
                      ** magic.
                      ** magic.
                   ++ eapply TySubst ; [
                        idtac
                      | eapply TySubst ; [
                          idtac
                        | eapply TySubst ; magic
                        | ..
                        ]
                      | ..
                      ].
                      ** magic.
                      ** eapply SubstCtxConv ; [
                           eapply SubstShift
                         | ..
                         ] ; try magic.
                         eapply EqCtxExtend ; [ magic .. | idtac ].
                         pushsubst1 ; magic.
                      ** magic.
                      ** magic.
                      ** magic.
                      ** magic.
                -- magic.
                -- magic.
                -- eapply TySubst ; [
                     idtac
                   | eapply TySubst ; [
                       idtac
                     | eapply TySubst ; magic
                     | ..
                     ]
                   | ..
                   ] ; try magic.
                   eapply SubstCtxConv ; [
                     eapply SubstShift
                   | ..
                   ] ; try magic.
                   eapply EqCtxExtend ; [ magic .. | idtac ].
                   pushsubst1 ; magic.
              * magic.
              * magic.
            + apply EqTyRefl ; [ magic | .. ].
              eapply TySubst ; [
                idtac
              | eapply TySubst ; [
                  idtac
                | eapply TySubst ; magic
                | ..
                ]
              | ..
              ] ; try magic.
              eapply SubstCtxConv ; [
                eapply SubstShift
              | ..
              ] ; try magic.
              eapply EqCtxExtend ; [ magic .. | idtac ].
              pushsubst1 ; magic.
            + magic.
            + eapply TySubst ; [
                idtac
              | eapply TySubst ; [
                  idtac
                | eapply TySubst ; magic
                | ..
                ]
              | ..
              ] ; try magic.
              eapply SubstCtxConv ; [
                eapply SubstShift
              | ..
              ] ; try magic.
              eapply EqCtxExtend ; [ magic .. | idtac ].
              pushsubst1 ; magic.
            + eapply TySubst ; [
                idtac
              | eapply TySubst ; [
                  idtac
                | eapply TySubst ; magic
                | ..
                ]
              | ..
              ] ; try magic.
              eapply SubstCtxConv ; [
                eapply SubstShift
              | ..
              ] ; try magic.
              eapply EqCtxExtend ; [ magic .. | idtac ].
              pushsubst1 ; magic.
          - magic.
          - magic.
          - magic.
          - magic.
          - magic.
          - magic.
          - magic.
          - magic.
          - magic.
          - magic.
          - magic.
          - eapply TySubst ; [
              idtac
            | eapply TySubst ; [
                idtac
              | eapply TySubst ; magic
              | ..
              ]
            | ..
            ] ; try magic.
            eapply SubstCtxConv ; [
              eapply SubstShift
            | ..
            ] ; try magic.
            eapply EqCtxExtend ; [ magic .. | idtac ].
            pushsubst1 ; magic.
          - magic.
          - magic.
          - eapply TySubst ; [
              idtac
            | eapply TySubst ; [
                idtac
              | eapply TySubst ; magic
              | ..
              ]
            | ..
            ] ; try magic.
            eapply SubstCtxConv ; [
              eapply SubstShift
            | ..
            ] ; try magic.
            eapply EqCtxExtend ; [ magic .. | idtac ].
            pushsubst1 ; magic.
          - magic.
          Unshelve. all:try strictmagic. all:try magic. all:exact w.
          Unshelve. all:try strictmagic. all:try magic.
          Unshelve. all:try strictmagic.
          all:eapply EqTyConv ; magic.
          Unshelve. all:try strictmagic.
          1:pushsubst1 ; try magic ; [
                  gocompsubst
                | eapply TermTyConv ; [
                    eapply TermSubst ; [
                      idtac
                    | eapply TermSubst ; magic
                    | ..
                    ]
                  | ..
                  ] ; magic
                ].
          all:pushsubst1 ; try magic.
          Unshelve. all:strictmagic.
        }
    }

  (* EqSubstExfalso *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstUnit *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstTrue *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstFalse *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstCond *)
  - { split.
      - { magic. }
      - { magic.
          Unshelve. all:strictmagic.
        }
    }

  (* EqTermExfalso *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* UnitEta *)
  - { split.
      - { assumption. }
      - { magic. }
    }

  (* EqReflection *)
  - { split.
      - { assumption. }
      - { magic. }
    }

  (* ProdBeta *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CondTrue *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CondFalse *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* ProdEta *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* JRefl *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongAbs *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongApp *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongRefl *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongJ *)
  - { split.
      - { magic. }
      - { trymagic.
          Unshelve. all:try magic.
          Unshelve. all:magic.
          Unshelve. all:strictmagic.
        }
    }

  (* CongCond *)
  - { split.
      - { magic. }
      - { magic. Unshelve. all:strictmagic. }
    }

  (* CongTermSubst *)
  - { split.
      - { magic. }
      - { magic. }
    }

Defined.

Theorem sane_eqterm G u v A :
  eqterm G u v A -> isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  intro H.
  destruct (sane_eqterm' G u v A H).
  auto using (@sane_isterm G u A).
Defined.
