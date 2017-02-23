(* Admissibile ptt rules. *)

Require Import syntax ptt ptt_tactics.



(* Some preliminary lemmata *)
Lemma EqTyWeakNat :
  forall {G D A B sbs},
    issubst sbs G D ->
    istype D A ->
    istype D B ->
    isctx G ->
    isctx D ->
    eqtype (ctxextend G (Subst A sbs))
           (Subst (Subst B sbweak) (sbshift sbs))
           (Subst (Subst B sbs) sbweak).
Proof.
  intros. magic.
  Unshelve. assumption.
Defined.


Lemma compWeakZero :
  forall {G A B u},
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u B ->
    eqtype G A (Subst A (sbcomp (sbweak) (sbzero u))).
Proof.
  intros. magic.
  Unshelve. assumption.
Defined.

Lemma EqTyWeakZero :
  forall {G A B u},
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u B ->
    eqtype G A (Subst (Subst A sbweak) (sbzero u)).
Proof.
  intros. magic.
  Unshelve. assumption.
Defined.

Lemma EqTyShiftZero :
  forall {G D A B v sbs},
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    isterm D v A ->
    isctx G ->
    isctx D ->
    eqtype
      G
      (Subst (Subst B (sbshift sbs)) (sbzero (subst v sbs)))
      (Subst (Subst B (sbzero v)) sbs).
Proof.
  intros. magic.
  Unshelve. all:strictmagic.
Defined.

Lemma EqTyCongZero :
  forall {G A1 A2 B1 B2 u1 u2},
    eqtype (ctxextend G A1) A2 B2 ->
    istype (ctxextend G A1) A2 ->
    istype (ctxextend G A1) B2 ->
    isctx G ->
    eqtype G A1 B1 ->
    eqterm G u1 u2 A1 ->
    istype G A1 ->
    istype G B1 ->
    isterm G u1 A1 ->
    isterm G u2 B1 ->
    eqtype G
           (Subst A2 (sbzero u1))
           (Subst B2 (sbzero u2)).
Proof.
  intros. magic.
Defined.

Lemma EqTyCongShift :
  forall {G1 G2 D A1 A2 B1 B2 sbs1 sbs2},
    eqctx G1 G2 ->
    eqsubst sbs1 sbs2 G1 D ->
    eqtype D A1 A2 ->
    eqtype (ctxextend D A1) B1 B2 ->
    isctx G1 ->
    isctx G2 ->
    isctx D ->
    issubst sbs1 G1 D ->
    issubst sbs2 G2 D ->
    istype D A1 ->
    istype D A2 ->
    istype (ctxextend D A1) B1 ->
    istype (ctxextend D A2) B2 ->
    eqtype (ctxextend G1 (Subst A1 sbs1))
           (Subst B1 (sbshift sbs1))
           (Subst B2 (sbshift sbs2)).
Proof.
  intros. magic.
  Unshelve. all:try strictmagic.
  (* I'm not very happy with the fact that I need to do it twice. *)
  (* But we have to blame the 'context' goal. *)
  all:strictmagic.
Defined.

Lemma EqTyCongWeak :
  forall {G1 G2 A1 A2 B1 B2},
    eqctx G1 G2 ->
    eqtype G1 A1 A2 ->
    eqtype G1 B1 B2 ->
    isctx G1 ->
    isctx G2 ->
    istype G1 A1 ->
    istype G1 B1 ->
    istype G2 A2 ->
    istype G2 B2 ->
    eqtype (ctxextend G1 A1)
           (Subst B1 sbweak)
           (Subst B2 sbweak).
Proof.
  intros. magic.
Defined.

Lemma EqSubstWeakNat :
  forall {G D A B u sbs},
    issubst sbs G D ->
    istype D A ->
    istype D B ->
    isterm D u B ->
    isctx G ->
    isctx D ->
    eqterm (ctxextend G (Subst A sbs))
           (subst (subst u sbweak) (sbshift sbs))
           (subst (subst u sbs) sbweak)
           (Subst (Subst B sbs) sbweak).
Proof.
  intros. magic.
  Unshelve. all:strictmagic.
Defined.

Lemma EqSubstWeakZero :
  forall {G A B u v},
    istype G A ->
    istype G B ->
    isterm G u A ->
    isterm G v B ->
    isctx G ->
    eqterm G
           (subst (subst u sbweak) (sbzero v))
           u
           A.
Proof.
  intros. magic.
  Unshelve. all:strictmagic.
Defined.

Lemma EqTermShiftZero :
  forall {G D A B u v sbs},
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    isterm (ctxextend D A) u B ->
    isterm D v A ->
    isctx G ->
    isctx D ->
    eqterm
      G
      (subst (subst u (sbshift sbs)) (sbzero (subst v sbs)))
      (subst (subst u (sbzero v)) sbs)
      (Subst (Subst B (sbzero v)) sbs).
Proof.
  intros. magic.
  Unshelve. all:strictmagic.
Defined.

Lemma EqTermCongWeak :
  forall {G1 G2 A1 A2 B1 B2 u1 u2},
    eqctx G1 G2 ->
    eqtype G1 A1 A2 ->
    eqtype G1 B1 B2 ->
    eqterm G1 u1 u2 B1 ->
    isctx G1 ->
    isctx G2 ->
    istype G1 A1 ->
    istype G1 B1 ->
    istype G2 B2 ->
    istype G2 A2 ->
    isterm G1 u1 B1 ->
    isterm G2 u2 B2 ->
    eqterm (ctxextend G1 A1)
           (subst u1 sbweak)
           (subst u2 sbweak)
           (Subst B1 sbweak).
Proof.
  intros. magic.
Defined.


(* Finally the lemma that we need to prove sanity of J. *)
Lemma JTyConv :
  forall {G D A C u v w p sbs},
    isctx G ->
    isctx D ->
    issubst sbs G D ->
    istype D A ->
    isterm D u A ->
    isterm D v A ->
    isterm D p (Id A u v) ->
    istype
      (ctxextend
         (ctxextend D A)
         (Id (Subst A sbweak) (subst u sbweak) (var 0))
      )
      C ->
    isterm
      D
      w
      (Subst
         (Subst
            C
            (sbshift (sbzero u)))
         (sbzero (refl A u))) ->
    isterm D p (Id A u v) ->
    eqtype
      G
      (Subst
         (Subst
            (Subst C
                   (sbshift (sbzero v)
                   )
            )
            (sbzero p)
         )
         sbs
      )
      (Subst
         (Subst
            (Subst C
                   (sbshift
                      (sbshift sbs)
                   )
            )
            (sbshift
               (sbzero (subst v sbs))
            )
         )
         (sbzero
            (subst p sbs)
         )
      ).
Proof.
  intros.
  (*! First let's have some assertions that we won't keep proving. !*)
  assert (isterm D (refl A u) (Id A u u)).
  { now apply TermRefl. }
  assert (
    istype (ctxextend D A)
           (Id (Subst A sbweak) (subst u sbweak) (var 0))
  ).
  { apply TyId ; magic. }
  assert (eqctx D D).
  { now apply CtxRefl. }
  assert (eqtype D (Subst (Subst A sbweak) (sbzero v)) A).
  { magic. Unshelve. assumption. }
  assert (isterm D u (Subst (Subst A sbweak) (sbzero v))).
  { magic. Unshelve. assumption. }
  assert (
    eqterm D
           (subst (subst u sbweak) (sbzero v)) u
           (Subst (Subst A sbweak) (sbzero v))
  ).
  { eapply EqSubstWeakZero ; try assumption ; magic.
    Unshelve. assumption.
  }
  assert (isterm D (subst (var 0) (sbzero v)) A).
  { eapply TermTyConv ; [
      eapply TermSubst ; magic
    | magic ..
    ].
  }
  assert (eqterm D (subst (var 0) (sbzero v)) v
    (Subst (Subst A sbweak) (sbzero v))).
  { eapply EqTyConv ; [
      eapply EqSubstZeroZero ; magic
    | magic ..
    ].
    Unshelve. all:assumption.
  }
  assert (isterm D v (Subst (Subst A sbweak) (sbzero v))).
  { eapply TermTyConv ; [ eassumption | magic .. ]. }
  assert (
    eqtype
      D
      (Id
         (Subst (Subst A sbweak) (sbzero v))
         (subst (subst u sbweak) (sbzero v))
         (subst (var 0) (sbzero v)))
      (Id A u v)
  ).
  { magic. }
  assert (
    eqtype D
    (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
       (sbzero v)) (Id A u v)
  ).
  { gopushsubst. }
  assert (
    eqctx
      (ctxextend
         D
         (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
                (sbzero v)))
      (ctxextend D (Id A u v))
  ).
  { magic. }
  assert (isctx (ctxextend D A)).
  { now apply CtxExtend. }
  assert (isctx
    (ctxextend (ctxextend D A)
       (Id (Subst A sbweak) (subst u sbweak) (var 0)))).
  { now apply CtxExtend. }
  assert (isterm G (refl (Subst A sbs) (subst u sbs))
    (Id (Subst A sbs) (subst u sbs) (subst u sbs))).
  { apply TermRefl ; magic. }
  assert (
    isterm (ctxextend G (Subst A sbs)) (var 0)
    (Subst (Subst A sbs) sbweak)
  ).
  { apply TermVarZero ; magic. }
  assert (istype (ctxextend G (Subst A sbs))
    (Id (Subst (Subst A sbs) sbweak)
       (subst (subst u sbs) sbweak) (var 0))
  ).
  { apply TyId ; magic. }
  assert (eqctx G G).
  { apply CtxRefl. assumption. }
  assert (
    eqsubst
      (sbcomp
         sbs
         (sbcomp
            sbweak
            (sbzero (subst v sbs)))
      )
      sbs
      G D
  ).
  { eapply SubstTrans ; [
      eapply CongSubstComp ; [
        eapply WeakZero ; magic
      | eapply SubstRefl ; magic
      | magic ..
      ]
    | magic ..
    ].
    Unshelve. all:strictmagic.
  }
  assert (eqtype D A A).
  { apply EqTyRefl ; assumption. }
  assert (eqtype G
    (Subst (Subst (Subst A sbs) sbweak)
       (sbzero (subst v sbs))) (Subst A sbs)).
  { gocompsubst.
    Unshelve. all:strictmagic.
  }
  assert (eqterm D u u A).
  { apply EqRefl ; assumption. }
  assert (
    eqsubst
      (sbcomp sbs
              (sbcomp sbweak
                      (sbzero (subst v sbs))
              )
      )
      (sbcomp sbweak (sbcomp (sbzero v) sbs))
      G
      D
  ).
  { eapply SubstTrans ; [
      eapply CongSubstComp ; [
        eapply WeakZero ; magic
      | eapply SubstRefl ; magic
      | magic ..
      ]
    | magic ..
    ].
    Unshelve. all:strictmagic.
  }
  assert (
    eqtype G
           (Subst A
                  (sbcomp sbs
                          (sbcomp sbweak
                                  (sbzero (subst v sbs))
                          )
                  )
           )
           (Subst A
                  (sbcomp sbweak
                          (sbcomp (sbzero v) sbs)
                  )
           )
  ).
  { eapply CongTySubst ; [ eassumption | magic .. ]. }
  assert (
    isterm G
           (subst u sbs)
           (Subst (Subst A sbs)
                  (sbcomp sbweak
                          (sbzero (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
  }
  assert (
    isterm G
           (subst (subst (subst u sbs) sbweak)
                  (sbzero (subst v sbs)))
           (Subst (Subst A sbs)
                  (sbcomp sbweak
                          (sbzero (subst v sbs))))
  ).
  { magic.
    Unshelve. all:strictmagic.
  }
  assert (
    eqsubst
      (sbcomp sbs
              (sbcomp
                 (sbcomp sbweak
                         (sbzero (subst v sbs)))
                 (sbcomp sbweak
                         (sbzero (subst v sbs)))))
      (sbcomp sbs
              (sbcomp sbweak
                      (sbzero (subst v sbs))))
      G
      D
  ).
  { eapply CongSubstComp ; [
      eapply SubstTrans ; [
        eapply CongSubstComp ; [
          eapply WeakZero ; magic
        | eapply SubstRefl ; magic
        | magic ..
        ]
      | magic ..
      ]
    | eapply SubstRefl ; magic
    | magic ..
    ].
    Unshelve. all:strictmagic.
  }
  assert (
    eqtype G
           (Subst A
                  (sbcomp sbs
                          (sbcomp
                             (sbcomp sbweak
                                     (sbzero (subst v sbs)))
                             (sbcomp sbweak
                                     (sbzero (subst v sbs))))))
           (Subst A
                  (sbcomp sbs
                          (sbcomp sbweak
                                  (sbzero (subst v sbs)))))
  ).
  { eapply CongTySubst ; [ eassumption | magic .. ]. }
  assert (
    isterm G
           (subst (subst u sbs)
                  (sbcomp sbweak
                          (sbzero (subst v sbs))
                  )
           )
           (Subst A
                  (sbcomp sbs
                          (sbcomp sbweak
                                  (sbzero (subst v sbs))
                          )
                  )
           )
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
  }
  assert (
    isterm G
           (subst u sbs)
           (Subst A
                  (sbcomp sbs
                          (sbcomp sbweak
                                  (sbzero (subst v sbs)))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
    Unshelve. all:strictmagic.
  }
  assert (
    eqterm G
    (subst (subst (subst u sbs) sbweak)
       (sbzero (subst v sbs))) (subst u sbs)
    (Subst (Subst (Subst A sbs) sbweak)
       (sbzero (subst v sbs)))
  ).
  { gocompsubst.
    Unshelve. all:strictmagic.
  }
  assert (
    isterm G
           (subst (var 0) (sbzero (subst v sbs)))
           (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    eqterm G (subst (var 0) (sbzero (subst v sbs)))
    (subst v sbs)
    (Subst (Subst (Subst A sbs) sbweak)
       (sbzero (subst v sbs)))
  ).
  { eapply EqTyConv ; [
      eapply EqSubstZeroZero ; magic
    | eapply EqTySym ; try magic ; eassumption
    | magic ..
    ].
    Unshelve. magic.
  }
  assert (
    eqtype G (Subst (Subst (Subst A sbweak) (sbzero v)) sbs)
    (Subst (Subst (Subst A sbs) sbweak)
       (sbzero (subst v sbs)))
  ).
  { magic. }
  assert (
    isterm G (subst u sbs)
    (Subst (Subst (Subst A sbs) sbweak)
       (sbzero (subst v sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    isterm G
           (subst v sbs)
           (Subst (Subst (Subst A sbs) sbweak)
                  (sbzero (subst v sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    eqtype G
           (Subst
              (Id (Subst (Subst A sbs) sbweak)
                  (subst (subst u sbs) sbweak)
                  (var 0)) (sbzero (subst v sbs)))
           (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { magic. }
  assert (
    eqctx
    (ctxextend G
       (Subst
          (Id (Subst (Subst A sbs) sbweak)
             (subst (subst u sbs) sbweak)
             (var 0)) (sbzero (subst v sbs))))
    (ctxextend G (Id (Subst A sbs) (subst u sbs) (subst v sbs)))
  ).
  { magic. }
  assert (isctx (ctxextend G (Subst A sbs))).
  { magic. }
  assert (
    eqtype (ctxextend G (Subst A sbs))
    (Subst (Subst A sbweak) (sbshift sbs))
    (Subst (Subst A sbs) sbweak)
  ).
  { eapply EqTyWeakNat ; eassumption. }
  assert (
    eqtype (ctxextend G (Subst A sbs))
           (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbs)
                  sbweak)
           (Subst (Subst A sbweak) (sbshift sbs))
  ).
  { eapply EqTySym ; magic.
    Unshelve. all:strictmagic.
  }
  assert (
    eqsubst
    (sbcomp sbweak
       (sbcomp (sbzero v) (sbcomp sbs sbweak)))
    (sbcomp sbweak
       (sbcomp (sbzero v) (sbcomp sbweak (sbshift sbs))))
    (ctxextend G (Subst A sbs)) D
  ).
  { eapply CongSubstComp ; [
      eapply CongSubstComp ; [
        eapply SubstSym ; magic
      | eapply SubstRefl ; magic
      | magic ..
      ]
    | eapply SubstRefl ; magic
    | magic ..
    ].
    Unshelve. all:strictmagic.
  }
  assert (
    eqtype (ctxextend G (Subst A sbs))
    (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbweak)
       (sbshift sbs))
    (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbs)
       sbweak)
  ).
  { (* For some reason I would assume this proof should be magicable. *)
    gocompsubst. gocompsubst. gocompsubst. gocompsubst. gocompsubst.
    gocompsubst. simplify ; try magic. simplify ; try magic.
    eapply EqTySym ; magic.
    Unshelve. all:strictmagic.
  }
  assert (
    isterm (ctxextend G (Subst A sbs))
    (subst (subst u sbweak) (sbshift sbs))
    (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbs)
       sbweak)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [ magic | eassumption | magic .. ]
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    eqtype (ctxextend G (Subst A sbs)) (Subst (Subst A sbs) sbweak)
    (Subst (Subst A sbweak) (sbshift sbs))
  ).
  { eapply EqTySym ; [
      eapply EqTyWeakNat ; magic
    | magic ..
    ].
  }
  assert (
    isterm (ctxextend G (Subst A sbs)) (subst (subst u sbweak) (sbshift sbs))
    (Subst (Subst A sbs) sbweak)
  ).
  { eapply TermTyConv ; magic. }
  assert (
    eqterm (ctxextend G (Subst A sbs))
    (subst (subst u sbweak) (sbshift sbs))
    (subst (subst u sbs) sbweak)
    (Subst (Subst A sbweak) (sbshift sbs))
  ).
  { eapply EqTyConv ; [
      eapply EqSubstWeakNat ; try magic ; eassumption
    | try magic ; try eassumption ..
    ].
    Unshelve. assumption.
  }
  assert (
    eqtype (ctxextend G (Subst A sbs))
           (Subst (Subst A sbs) sbweak)
           (Subst (Subst A sbweak) (sbshift sbs))
  ).
  { apply EqTySym ; magic. }
  assert (
    isterm (ctxextend G (Subst A sbs))
           (subst (var 0) (sbshift sbs))
           (Subst (Subst A sbs) sbweak)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermVarZero ; magic
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (eqterm (ctxextend G (Subst A sbs)) (subst (var 0) (sbshift sbs))
    (var 0) (Subst (Subst A sbweak) (sbshift sbs))).
  { eapply EqTyConv ; [
      eapply EqSubstShiftZero ; magic
    | magic ..
    ].
    Unshelve. assumption.
  }
  assert (
    isterm (ctxextend G (Subst A sbs))
    (subst (subst u sbs) sbweak)
    (Subst (Subst A sbweak) (sbshift sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [ magic | eassumption | magic .. ]
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    isterm (ctxextend G (Subst A sbs)) (var 0)
    (Subst (Subst A sbweak) (sbshift sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermVarZero ; magic
    | magic ..
    ].
  }
  assert (
    eqtype (ctxextend G (Subst A sbs))
    (Id (Subst (Subst A sbs) sbweak)
       (subst (subst u sbs) sbweak) (var 0))
    (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
       (sbshift sbs))
  ).
  { gopushsubst. }
  assert (
    eqctx
    (ctxextend (ctxextend G (Subst A sbs))
       (Id (Subst (Subst A sbs) sbweak)
          (subst (subst u sbs) sbweak)
          (var 0)))
    (ctxextend (ctxextend G (Subst A sbs))
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbshift sbs)))
  ).
  { magic.
    Unshelve. assumption.
  }
  assert (
    isterm (ctxextend D (Subst (Subst A sbweak) (sbzero v)))
    (var 0) (Subst A sbweak)
  ).
  { eapply TermTyConv ; magic. Unshelve. all:strictmagic. }
  assert (
    issubst
      (sbshift (sbzero v))
      (ctxextend D (Id A u v))
      (ctxextend
         (ctxextend D A)
         (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { eapply SubstCtxConv ; try magic ; try eassumption.
    Unshelve. all:strictmagic.
  }
  assert (istype D (Id A u v)).
  { magic. }
  assert (isctx (ctxextend G (Subst (Id A u v) sbs))).
  { magic. }
  assert (
    issubst (sbshift sbs) (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend D
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbzero v)))
  ).
  { eapply SubstCtxConv ; magic.
    Unshelve. all:try magic.
    Unshelve. all:try strictmagic.
    all:(eapply TermTyConv ; try strictmagic).
    all:(eapply EqTySym ; try strictmagic).
    all:(simplify ; try strictmagic).
    all:assumption.
  }
  assert (
    eqsubst (sbcomp sbweak (sbcomp (sbzero v) sbs)) sbs G D
  ).
  { eapply SubstTrans ; [
      eapply CompAssoc ; magic
    | eapply SubstTrans ; [
        eapply CongSubstComp ; [
          eapply SubstRefl ; magic
        | eapply WeakZero ; magic
        | magic ..
        ]
      | magic ..
      ]
    | magic ..
    ].
    Unshelve. all:assumption.
  }
  assert (
    eqtype G (Subst A (sbcomp sbweak (sbcomp (sbzero v) sbs)))
    (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbweak)
       (sbcomp (sbzero v) sbs))
  ).
  { gocompsubst. Unshelve. all:assumption. }
  assert (
    eqtype G
    (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbweak)
       (sbcomp (sbzero v) sbs))
    (Subst (Subst (Subst A sbweak) (sbzero v))
       (sbcomp sbweak (sbcomp (sbzero v) sbs)))
  ).
  { gocompsubst. Unshelve. all:assumption. }
  assert (
    isterm G
           (subst (subst u sbweak) (sbcomp (sbzero v) sbs))
           (Subst (Subst (Subst A sbweak) (sbzero v))
                  (sbcomp sbweak (sbcomp (sbzero v) sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [ magic | eassumption | magic .. ]
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    isterm G (subst u sbs)
    (Subst (Subst (Subst A sbweak) (sbzero v))
       (sbcomp sbweak (sbcomp (sbzero v) sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
    Unshelve. all:assumption.
  }
  assert (
    eqtype G (Subst (Subst (Subst A sbweak) (sbzero v)) sbs)
    (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbweak)
       (sbcomp (sbzero v) sbs))
  ).
  { gocompsubst. }
  assert (
    isterm G (subst u sbs)
    (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbweak)
       (sbcomp (sbzero v) sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    eqtype G
    (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbweak)
       (sbcomp (sbzero v) sbs)) (Subst A sbs)
  ).
  { gocompsubst. Unshelve. all:assumption. }
  assert (
    eqtype G (Subst (Subst A sbweak) (sbcomp (sbzero v) sbs)) (Subst A sbs)
  ).
  { gocompsubst. Unshelve. all:assumption. }
  assert (
    eqtype G (Subst (Subst A sbweak) (sbcomp (sbzero v) sbs))
    (Subst A (sbcomp sbweak (sbcomp (sbzero v) sbs)))
  ).
  { gocompsubst. Unshelve. all:assumption. }
  assert (
    eqtype G (Subst A sbs) (Subst (Subst A sbweak) (sbcomp (sbzero v) sbs))
  ).
  { gocompsubst. Unshelve. all:assumption. }
  assert (
    eqterm G (subst u sbs)
    (subst (subst u sbweak) (sbcomp (sbzero v) sbs))
    (Subst A sbs)
  ).
  { gocompsubst ; try eassumption ; try magic
    ; eapply TermTyConv ; magic.
    Unshelve. all:assumption.
  }
  assert (
     eqtype G (Subst (Subst A sbweak) (sbcomp (sbzero v) sbs))
    (Subst A sbs)
  ).
  { gocompsubst. Unshelve. all:assumption. }
  assert (
    isterm G (subst (var 0) (sbcomp (sbzero v) sbs)) (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermVarZero ; magic
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    eqtype G (Subst A sbs)
    (Subst (Subst A sbweak) (sbcomp (sbzero v) sbs))
  ).
  { gocompsubst. Unshelve. all:assumption. }
  assert (
    isterm G (subst (subst (var 0) (sbzero v)) sbs)
    (Subst (Subst A sbweak) (sbcomp (sbzero v) sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ eassumption | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    eqterm G
           (subst v sbs)
           (subst (var 0) (sbcomp (sbzero v) sbs))
           (Subst A sbs)
  ).
  { eapply EqSym ; magic.
    Unshelve. assumption.
  }
  assert (
     isterm G (subst (subst u sbweak) (sbcomp (sbzero v) sbs))
    (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [ magic | eassumption | magic .. ]
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    eqtype G
    (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
       (sbcomp (sbzero v) sbs)) (Subst (Id A u v) sbs)
  ).
  { magic. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbcomp (sbzero v) sbs))) (ctxextend G (Subst (Id A u v) sbs))
  ).
  { magic. }
  assert (
    eqsubst
    (sbcomp
       sbweak
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    sbs
    G D
  ).
  { eapply SubstTrans ; [
      eapply CongSubstComp ; [
        eapply ShiftZero ; magic
      | eapply SubstRefl ; magic
      | magic ..
      ]
    | magic ..
    ].
    Unshelve. all:assumption.
  }
  assert (
    eqtype G
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (Subst A sbs)
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    eqtype G
    (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (Subst A
       (sbcomp sbweak
          (sbcomp (sbshift sbs) (sbzero (subst v sbs)))))
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    eqtype
      G
      (Subst (Subst A sbweak) (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
      (Subst A (sbcomp sbweak (sbcomp (sbshift sbs) (sbzero (subst v sbs)))))
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    isterm G
    (subst (subst u sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (Subst A
       (sbcomp sbweak
          (sbcomp (sbshift sbs) (sbzero (subst v sbs)))))
  ).
  { eapply TermTyConv ; [
      (eapply TermSubst ; try magic) ;
      (eapply TermSubst ; try magic) ;
      eassumption
    | magic ..
    ].
  }
  assert (
    isterm G (subst u sbs)
    (Subst A
       (sbcomp sbweak
          (sbcomp (sbshift sbs) (sbzero (subst v sbs)))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
    Unshelve. all:strictmagic.
  }
  assert (
    eqterm G
    (subst (subst u sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (subst u sbs)
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    isterm (ctxextend D A) (var 0) (Subst A sbweak)
  ).
  { magic. }
  assert (
    eqtype G
    (Subst (Subst (Subst A sbweak) (sbshift sbs))
       (sbzero (subst v sbs)))
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { magic. Unshelve. all:assumption. }
  assert (
    isterm G
    (subst (subst (var 0) (sbshift sbs))
       (sbzero (subst v sbs)))
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
       | eapply TermSubst ; [
           magic
         | eapply TermVarZero ; magic
         | magic ..
        ]
       | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    eqtype G (Subst (Subst (Subst A sbweak) (sbzero v)) sbs)
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { magic. Unshelve. all:assumption. }
  assert (
    isterm G (subst v sbs)
   (Subst (Subst A sbweak)
      (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eassumption
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    eqsubst
      (sbcomp sbweak
              (sbcomp (sbshift sbs)
                      (sbzero (subst v sbs))))
      (sbcomp sbs
              (sbcomp sbweak
                      (sbzero (subst v sbs))))
      G
      D
  ).
  { eapply SubstTrans ; [
      eapply CompAssoc ; magic
    | try magic ..
    ].
    eapply SubstTrans ; [
      eapply CongSubstComp ; [
        eapply SubstRefl ; magic
      | eapply WeakNat ; magic
      | magic ..
      ]
    | try magic ..
    ].
    eapply SubstSym ; try magic.
    eapply SubstTrans ; [
      eapply CompAssoc ; magic
    | magic ..
    ].
    Unshelve. all:strictmagic.
  }
  assert (
     eqtype G
    (Subst (Subst (Subst A sbs) sbweak)
       (sbzero (subst v sbs)))
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    isterm G (subst (var 0) (sbzero (subst v sbs)))
   (Subst (Subst A sbweak)
      (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermVarZero ; magic
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    eqtype G (Subst A sbs)
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { magic. Unshelve. all:assumption. }
  assert (
    eqterm G
    (subst (var 0)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (subst v sbs)
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { eapply EqTrans ; [
      eapply EqSym ; [
        eapply EqSubstComp ; [ shelve | magic .. ]
      | magic ..
      ]
    | magic ..
    ].
    Unshelve. all:try strictmagic.
  }
  assert (
    isterm G (subst u sbs)
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    eqtype G
    (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (Subst (Id A u v) sbs)
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbcomp (sbshift sbs) (sbzero (subst v sbs)))))
    (ctxextend G (Subst (Id A u v) sbs))
  ).
  { magic. }
  assert (istype G (Id (Subst A sbs) (subst u sbs) (subst v sbs))).
  { magic. }
  assert (
    eqtype G (Id (Subst A sbs) (subst u sbs) (subst v sbs))
    (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { apply EqTyRefl ; assumption. }
  assert (
     eqtype G
            (Subst (Id A u v) sbs)
            (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { gopushsubst. }
  assert (
    isterm G (subst p sbs) (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    eqtype G
    (Subst
       (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbweak)
          (sbshift sbs)) (sbzero (subst v sbs)))
    (Subst A sbs)
  ).
  { gocompsubst. Unshelve. all:assumption. }
  assert (
    isterm G
    (subst (subst (subst u sbweak) (sbshift sbs))
       (sbzero (subst v sbs))) (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [
          magic
        | eapply TermSubst ; [ magic | eassumption | magic .. ]
        | magic ..
        ]
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    eqtype G
    (Subst (Subst (Subst A sbweak) (sbshift sbs))
       (sbzero (subst v sbs))) (Subst A sbs)
  ).
  { magic. }
  assert (
    isterm G
    (subst (subst (var 0) (sbshift sbs))
       (sbzero (subst v sbs))) (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [ magic | eassumption | magic .. ]
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    eqtype G (Subst A sbs)
    (Subst (Subst (Subst A sbweak) (sbshift sbs))
       (sbzero (subst v sbs)))
  ).
  { magic. }
  assert (
    eqtype G
    (Subst
       (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbweak)
          (sbshift sbs)) (sbzero (subst v sbs)))
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { magic. Unshelve. all:assumption. }
  assert (
    isterm G
    (subst (subst (subst u sbweak) (sbshift sbs))
       (sbzero (subst v sbs)))
    (Subst (Subst A sbweak)
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [
          magic
        | eapply TermSubst ; [ magic | eassumption | magic .. ]
        | magic ..
        ]
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    eqsubst
    (sbcomp sbweak
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (sbcomp sbweak (sbcomp (sbzero v) sbs)) G D
  ).
  { eapply CongSubstComp ; magic. Unshelve. all:assumption. }
  assert (
    eqtype G (Subst (Subst (Subst A sbweak) (sbzero v)) sbs)
    (Subst (Subst (Subst A sbweak) (sbshift sbs))
       (sbzero (subst v sbs)))
  ).
  { gocompsubst. Unshelve. all:assumption. }
  assert (
    isterm G (subst u sbs)
    (Subst (Subst (Subst A sbweak) (sbshift sbs))
       (sbzero (subst v sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    eqterm G (subst u sbs)
    (subst (subst (subst u sbweak) (sbshift sbs))
       (sbzero (subst v sbs))) (Subst A sbs)
  ).
  { gocompsubst ; try eassumption ; magic. }
  assert (
    isterm G (subst v sbs)
    (Subst (Subst (Subst A sbweak) (sbshift sbs))
       (sbzero (subst v sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    eqterm G (subst v sbs)
    (subst (subst (var 0) (sbshift sbs))
       (sbzero (subst v sbs))) (Subst A sbs)
  ).
  { eapply EqSym ; try magic. }
  assert (
    eqtype G
    (Subst
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbshift sbs)) (sbzero (subst v sbs)))
    (Subst (Id A u v) sbs)
  ).
  { magic. }
  assert (
    eqctx
    (ctxextend G
       (Subst
          (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
             (sbshift sbs)) (sbzero (subst v sbs))))
    (ctxextend G (Subst (Id A u v) sbs))
  ).
  { magic. }
  assert (
    isctx
    (ctxextend (ctxextend G (Subst A sbs))
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbshift sbs)))
  ).
  { magic. }
  assert (
    eqctx
      (ctxextend
         G
         (Subst
            (Id (Subst (Subst A sbweak) (sbshift sbs))
                (subst (subst u sbweak) (sbshift sbs))
                (subst (var 0) (sbshift sbs)))
            (sbzero (subst v sbs)))) (ctxextend G (Subst (Id A u v) sbs))
  ).
  { magic. }
  assert (
    istype G
   (Subst
      (Subst
         (Subst C
            (sbshift
               (sbshift sbs)))
         (sbshift (sbzero (subst v sbs))))
      (sbzero (subst p sbs)))
  ).
  { eapply TySubst ; try magic.
    eapply TySubst ; try magic.
    eapply SubstCtxConv ; [
      eapply SubstShift ; magic
    | try magic ..
    ].
    eassumption.
    Unshelve. all:strictmagic.
  }
  assert (
    eqtype G
    (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbshift sbs))
       (sbzero (subst v sbs))) (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { magic. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbshift sbs))
          (sbzero (subst v sbs))))
    (ctxextend G (Id (Subst A sbs) (subst u sbs) (subst v sbs)))
  ).
  { magic. }
  assert (
    issubst
    (sbshift (sbzero (subst v sbs)))
    (ctxextend G (Id (Subst A sbs) (subst u sbs) (subst v sbs)))
    (ctxextend (ctxextend G (Subst A sbs))
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbshift sbs)))
  ).
  { assert (issubst (sbcomp sbweak (sbshift sbs)) (ctxextend G (Subst A sbs)) D)
      by magic.
    eapply SubstCtxConv ; [
      eapply SubstShift ; magic
    | try magic ..
    ].

    Unshelve.
    all:try strictmagic.
    all:try magic.
    Unshelve. all:try strictmagic.
  }
  assert (
    issubst
    (sbshift sbs) (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend D (Id A u v))
  ).
  { eapply SubstCtxConv ; magic.
    Unshelve. all:try strictmagic.
    all:magic.
    Unshelve. all:strictmagic.
  }
  assert (
    eqtype G
    (Subst
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbzero v)) sbs)
    (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
       (sbcomp (sbzero v) sbs))
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    eqctx
    (ctxextend G
       (Subst
          (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
             (sbzero v)) sbs))
    (ctxextend G
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbcomp (sbzero v) sbs)))
  ).
  { eapply EqCtxExtend ; magic. }
  assert (
    issubst
   (sbcomp
      (sbshift
         (sbzero v))
      (sbshift sbs))
   (ctxextend G
      (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
         (sbcomp (sbzero v) sbs)))
   (ctxextend (ctxextend D A)
      (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { eapply SubstCtxConv ; magic. Unshelve. all:try strictmagic. all:magic.
    Unshelve. all:strictmagic.
  }
  assert (
    issubst
    (sbshift
       (sbcomp (sbzero v) sbs)) (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend (ctxextend D A)
       (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { eapply SubstCtxConv ; magic. Unshelve. all:try strictmagic.
    all:magic. Unshelve. all:strictmagic.
  }
  assert (
    issubst
    (sbshift
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (ctxextend G
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbcomp (sbzero v) sbs)))
    (ctxextend (ctxextend D A)
       (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { magic. Unshelve. all:try strictmagic. all:magic.
    Unshelve. all:strictmagic.
  }
  assert (
    issubst
    (sbshift
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend (ctxextend D A)
       (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    eqtype G
    (Subst
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbshift sbs)) (sbzero (subst v sbs)))
    (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    eqctx
    (ctxextend G
       (Subst
          (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
             (sbshift sbs)) (sbzero (subst v sbs))))
    (ctxextend G
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbcomp (sbshift sbs) (sbzero (subst v sbs)))))
  ).
  { magic. }
  assert (
    issubst
   (sbcomp
      (sbshift
         (sbshift sbs))
      (sbshift (sbzero (subst v sbs))))
   (ctxextend G
      (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
         (sbcomp (sbshift sbs) (sbzero (subst v sbs)))))
   (ctxextend (ctxextend D A)
      (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { eapply SubstCtxConv ; try magic. Unshelve. all:try strictmagic.
    all:magic. Unshelve. all:strictmagic.
  }
  assert (
    issubst
    (sbcomp
       (sbshift
          (sbshift sbs))
       (sbshift (sbzero (subst v sbs))))
    (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend (ctxextend D A)
       (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { magic. Unshelve. all:try strictmagic. all:try magic.
    Unshelve. all:try strictmagic. all:magic.
    Unshelve. all:strictmagic.
  }
  assert (
    issubst
    (sbshift (sbzero (subst v sbs)))
    (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend (ctxextend G (Subst A sbs))
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbshift sbs)))
  ).
  { magic. Unshelve. all:try strictmagic. all:magic.
    Unshelve. all:strictmagic.
  }
  assert (
    issubst
   (sbshift (sbzero (subst v sbs)))
   (ctxextend G
      (Subst
         (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
            (sbshift sbs)) (sbzero (subst v sbs))))
   (ctxextend (ctxextend G (Subst A sbs))
      (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
         (sbshift sbs)))
  ).
  { magic. }
  assert (
    issubst
      (sbzero
              (subst p sbs)
      )
      G
      (ctxextend G (Subst (Id A u v) sbs))
  ).
  { magic. }
  assert (
    eqtype G
    (Subst
       (Subst (Subst (Subst (Subst A sbweak) (sbzero v)) sbs)
          sbweak) (sbzero (subst v sbs)))
    (Subst A sbs)
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    isterm G
    (subst (subst (subst u sbs) sbweak)
       (sbzero (subst v sbs))) (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [
          magic
        | eapply TermSubst ; [ magic | eassumption | magic .. ]
        | magic ..
        ]
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (
    eqtype G (Subst A sbs)
   (Subst (Subst (Subst A sbs) sbweak)
      (sbzero (subst v sbs)))
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
     eqterm G (subst u sbs)
   (subst (subst (subst u sbs) sbweak)
      (sbzero (subst v sbs))) (Subst A sbs)
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
     eqterm G
            (subst v sbs)
            (subst (var 0) (sbzero (subst v sbs)))
            (Subst A sbs)
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    eqtype G
    (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbcomp (sbzero v) sbs))
    (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbzero v)) sbs)
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbcomp (sbzero v) sbs)))
    (ctxextend G
       (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbzero v))
          sbs))
  ).
  { magic. }
  assert (
    issubst (sbshift (sbcomp (sbzero v) sbs))
   (ctxextend G
      (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbzero v)) sbs))
   (ctxextend (ctxextend D A) (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { magic. Unshelve. all:try strictmagic. all:magic.
    Unshelve. all:strictmagic.
  }
  assert (
    eqtype G
    (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
       (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbzero v)) sbs)
  ).
  { magic. Unshelve. all:strictmagic. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
          (sbcomp (sbshift sbs) (sbzero (subst v sbs)))))
    (ctxextend G
       (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbzero v))
          sbs))
  ).
  { magic. }
  assert (
    issubst (sbshift (sbcomp (sbshift sbs) (sbzero (subst v sbs))))
    (ctxextend G
       (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbzero v))
          sbs))
    (ctxextend (ctxextend D A) (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { magic. Unshelve. all:try strictmagic. all:magic.
    Unshelve. all:strictmagic.
  }
  assert (
    eqtype G
    (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbshift sbs))
       (sbzero (subst v sbs)))
    (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbzero v)) sbs)
  ).
  { magic. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbshift sbs))
          (sbzero (subst v sbs))))
    (ctxextend G
       (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbzero v))
          sbs))
  ).
  { magic. }
  assert (
    issubst (sbcomp (sbshift (sbshift sbs)) (sbshift (sbzero (subst v sbs))))
    (ctxextend G
       (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbzero v))
          sbs))
    (ctxextend (ctxextend D A) (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { magic. Unshelve. all:try strictmagic. all:try magic.
    Unshelve. all:try strictmagic. all:try magic.
    Unshelve. all:strictmagic.
  }
  assert (
    issubst (sbcomp (sbshift (sbshift sbs)) (sbshift (sbzero (subst v sbs))))
   (ctxextend G
      (Subst (Subst (Id (Subst A sbweak) (subst u sbweak) (var 0)) (sbzero v)) sbs))
   (ctxextend (ctxextend D A) (Id (Subst A sbweak) (subst u sbweak) (var 0)))
  ).
  { magic. }
  (*! Now let's proceed with the proof. !*)
  (* We start by composing all the substitutions so we can forget about
     the types. *)
  gocompsubst ; try assumption.
  gocompsubst ; try assumption.
  gocompsubst ; try assumption.
  gocompsubst ; try assumption.
  (* Now we can focus on susbtitutions. *)
  eapply CongTySubst ; try magic.
  (* We go from the rhs. *)
  eapply SubstSym ; try magic.
  eapply SubstTrans ; [
    (* Then we only look on the lhs of the composition. *)
    eapply CongSubstComp ; [
      (* We exchange the substitutionss. *)
      eapply SubstSym ; [
        eapply ShiftZero ; magic
      | magic ..
      ]
    | (* We don't touch the rhs. *)
    eapply SubstRefl ; magic
    | magic ..
    ]
  | try magic ..
  ].
  (* We're using associativity to look at the rhs. *)
  eapply SubstTrans ; [
    eapply CompAssoc ; magic
  | try magic ..
  ].
  (* We can now have a look at the rhs of the composition. *)
  eapply SubstTrans ; [
    eapply CongSubstComp ; [
      (* On the left we remain unchanged. *)
      eapply SubstRefl ; magic
    | (* On the right we have a composition of shifts, thus we use
         fonctoriality to progress.
         However we need to apply congruence again to rewrite
         the type in the left shift. *)
    eapply CongSubstComp ; [
      (* eapply @CongSubstShift *)
      (* with (A2 := Subst *)
      (*              (Id (Subst A sbweak) *)
      (*                  (subst u sbweak) *)
      (*                  (var 0)) *)
      (*              (sbzero v) *)
      (*      ) *)
      eapply CongSubstShift ; try magic ;
      (apply CtxRefl ; magic)
    | (* We don't change the other substitution. *)
    apply SubstRefl ; magic
    | magic ..
    ]
    | magic ..
    ]
  | try magic ..
  ].
  (* Now that we rewrote the type, we can use fonctoriality. *)
  (* Note this could be meged with the next couple steps. *)
  eapply SubstTrans ; [
    eapply CongSubstComp ; [
      (* On the left we remain unchanged. *)
      eapply SubstRefl ; magic
    | eapply EqSubstCtxConv ; [
        eapply CompShift ; magic
      | try magic ; eassumption ..
      ]
    | magic ..
    ]
  | try magic ..
  ].
  (* Now that we have a composition inside the shift, we want
     to proceed with an exchange by using ShiftZero. *)
  eapply SubstTrans ; [
    eapply CongSubstComp ; [
      (* We leave the left unchanged. *)
      eapply SubstRefl ; magic
    | eapply EqSubstCtxConv ; [
        eapply CongSubstShift ; [
          eapply SubstSym ; [
            eapply ShiftZero ; magic
          | magic ..
          ]
        | magic ..
        ]
      | try magic ; eassumption ..
      ]
    | magic ..
    ]
  | try magic ..
  ].
  (* Now we need to apply CompShift again to put the composition outside
     and apply associativity. *)
  eapply SubstTrans ; [
    eapply CongSubstComp ; [
      (* On the left we remain unchanged. *)
      eapply SubstRefl ; magic
    | eapply SubstSym ; [
        eapply EqSubstCtxConv ; [
          eapply CompShift ; magic
        | try magic ; eassumption ..
        ]
      | magic ..
      ]
    | magic ..
    ]
  | try magic ..
  ].
  (* Now, it's time to apply associativity guys. *)
  eapply SubstTrans ; [
    eapply SubstSym ; [
      eapply CompAssoc ; magic
    | magic ..
    ]
  | try magic ..
  ].
  (* Now we should finally have the same structure for the substitutions
     and thus be able to apply congruences. *)
  eapply CongSubstComp ; try magic.
  eapply CongSubstComp ; try magic ; try assumption.
  eapply EqSubstCtxConv ; [
    eapply CongSubstShift ; magic
  | try magic ; assumption ..
  ].
  Unshelve. all:try strictmagic. all:try magic.
  Unshelve. all:try strictmagic.
  all:eapply TermTyConv ; [ exact H5 | .. ] ; magic.
  (* This is all because of the asserts eveywhere. *)
Defined.
