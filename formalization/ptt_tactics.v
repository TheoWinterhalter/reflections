(* Tactics and auxiliary lemmas for ptt. *)
Require Import syntax ptt.

(* Some tactic to compose substitutions. *)
Lemma eqtype_subst_left :
  forall {G D E A B sbs sbt},
    issubst sbs G D ->
    issubst sbt D E ->
    istype E A ->
    eqtype G (Subst A (sbcomp sbt sbs)) B ->
    istype G B ->
    isctx G ->
    isctx D ->
    isctx E ->
    (* istype G (Subst (Subst A sbt) sbs) -> *)
    (* istype G (Subst A (sbcomp sbt sbs)) -> *)
    eqtype G (Subst (Subst A sbt) sbs) B.
Proof.
  intros.
  eapply EqTyTrans ; [
    eapply EqTySubstComp ; eassumption
  | try assumption ..
  ].
  - eapply TySubst ; try eassumption.
    eapply TySubst ; eassumption.
  - eapply TySubst ; try eassumption.
    eapply SubstComp ; eassumption.
Defined.

Lemma eqterm_subst_left :
  forall {G D E A u v sbs sbt},
    issubst sbs G D ->
    issubst sbt D E ->
    isterm E u A ->
    istype E A ->
    eqterm G (subst u (sbcomp sbt sbs)) v (Subst A (sbcomp sbt sbs)) ->
    isctx G ->
    isctx D ->
    isctx E ->
    (* istype G (Subst (Subst A sbt) sbs) -> *)
    (* istype G (Subst A (sbcomp sbt sbs)) -> *)
    (* isterm G (subst (subst u sbt) sbs) (Subst A (sbcomp sbt sbs)) -> *)
    (* isterm G (subst u (sbcomp sbt sbs)) (Subst A (sbcomp sbt sbs)) -> *)
    isterm G v (Subst A (sbcomp sbt sbs)) ->
    eqterm G (subst (subst u sbt) sbs) v (Subst (Subst A sbt) sbs).
Proof.
  intros.
  assert (istype G (Subst (Subst A sbt) sbs)).
  { eapply TySubst ; try eassumption.
    eapply TySubst ; eassumption. }
  assert (istype G (Subst A (sbcomp sbt sbs))).
  { eapply TySubst ; try eassumption.
    eapply SubstComp ; eassumption. }
  assert (isterm G (subst (subst u sbt) sbs) (Subst A (sbcomp sbt sbs))).
  { eapply TermTyConv.
    - eapply TermSubst ; try eassumption.
      + eapply TermSubst ; eassumption.
      + eapply TySubst ; eassumption.
    - eapply eqtype_subst_left ; try eassumption.
      eapply EqTyRefl ; eassumption.
    - assumption.
    - assumption.
    - assumption.
  }
  assert (isterm G (subst u (sbcomp sbt sbs)) (Subst A (sbcomp sbt sbs))).
  { eapply TermSubst ; try eassumption.
    eapply SubstComp ; eassumption.
  }

  assert (hh : eqtype G (Subst A (sbcomp sbt sbs)) (Subst (Subst A sbt) sbs)).
  { apply EqTySym ; [
      eapply EqTySubstComp ; eassumption
    | assumption ..
    ].
  }
  assert (h : eqterm G (subst u (sbcomp sbt sbs)) v (Subst (Subst A sbt) sbs)).
  { eapply EqTyConv ; eassumption. }
  eapply EqTrans.
  - eapply EqTyConv.
    + eapply EqSubstComp ; eassumption.
    + apply EqTySym ; [
        eapply EqTySubstComp ; eassumption
      | assumption ..
      ].
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
  - assumption.
  - assumption.
  - assumption.
  - eapply TermTyConv ; eassumption.
  - eapply TermTyConv ; eassumption.
  - eapply TermTyConv ; eassumption.
Defined.

Ltac compsubst1 :=
  lazymatch goal with
  | |- eqtype ?G (Subst (Subst ?A ?sbt) ?sbs) ?B =>
    eapply eqtype_subst_left
  | |- eqtype ?G ?A (Subst (Subst ?B ?sbt) ?sbs) =>
    eapply EqTySym ; [ eapply eqtype_subst_left | .. ]
  | |- eqterm ?G (subst (subst ?u ?sbt) ?sbs) ?v (Subst (Subst ?A ?sbt) ?sbs) =>
    eapply eqterm_subst_left
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) (Subst (Subst ?A ?sbt) ?sbs) =>
    eapply EqSym ; [ eapply eqterm_subst_left | .. ]
  | |- eqterm ?G (subst (subst ?u ?sbt) ?sbs) ?v ?A =>
    eapply EqTyConv ; [ eapply eqterm_subst_left | .. ]
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) ?A =>
    eapply EqSym ; [
      eapply EqTyConv ; [ eapply eqterm_subst_left | .. ]
    | ..
    ]
  | |- ?G => fail "Not a goal handled by compsubst" G
  end.


Lemma EqCompZero :
  forall {G D A u sbs},
    issubst sbs G D ->
    isterm D u A ->
    istype D A ->
    isctx G ->
    isctx D ->
    eqterm G
           (subst (var 0) (sbcomp (sbzero D A u) sbs))
           (subst u sbs)
           (Subst A sbs).
Proof.
  intros.
  assert (istype G (Subst A sbs)).
  { eapply TySubst ; eassumption. }
  assert (isterm G (subst u sbs) (Subst A sbs)).
  { eapply TermSubst ; eassumption. }
  assert (issubst (sbzero D A u) D (ctxextend D A)).
  { eapply SubstZero ; eassumption. }
  assert (isctx (ctxextend D A)).
  { eapply CtxExtend ; assumption. }
  assert (issubst (sbcomp (sbzero D A u) sbs) G (ctxextend D A)).
  { eapply SubstComp ; eassumption. }
  assert (isterm (ctxextend D A) (var 0) (Subst A (sbweak D A))).
  { apply TermVarZero ; assumption. }
  assert (issubst (sbweak D A) (ctxextend D A) D).
  { eapply SubstWeak ; assumption. }
  assert (istype (ctxextend D A) (Subst A (sbweak D A))).
  { eapply TySubst ; eassumption. }
  assert (
    isterm G
           (subst (var 0) (sbcomp (sbzero D A u) sbs))
           (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A u) sbs))
  ).
  { eapply TermSubst ; eassumption. }
  assert (istype G (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A u) sbs))).
  { eapply TySubst ; eassumption. }
  assert (issubst (sbcomp (sbweak D A) (sbcomp (sbzero D A u) sbs)) G D).
  { eapply SubstComp ; eassumption. }
  assert (istype G (Subst A (sbcomp (sbweak D A) (sbcomp (sbzero D A u) sbs)))).
  { eapply TySubst ; eassumption. }
  assert (issubst (sbcomp (sbweak D A) (sbzero D A u)) D D).
  { eapply SubstComp ; eassumption. }
  assert (issubst (sbid D) D D).
  { apply SubstId. assumption. }
  assert (issubst (sbcomp (sbcomp (sbweak D A) (sbzero D A u)) sbs) G D).
  { eapply SubstComp ; eassumption. }
  assert (issubst (sbcomp (sbid D) sbs) G D).
  { eapply SubstComp ; eassumption. }
  assert (eqsubst (sbcomp (sbweak D A) (sbcomp (sbzero D A u) sbs)) sbs G D).
  { eapply SubstTrans ; [
      eapply CompAssoc
    | eapply SubstTrans ; [
        eapply CongSubstComp ; [
          eapply SubstRefl
        | eapply WeakZero
        | ..
        ]
      | eapply CompIdLeft
      | ..
      ]
    | ..
    ] ; eassumption.
  }
  assert (eqtype D A A).
  { eapply EqTyRefl ; assumption. }
  assert (
    eqtype G (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A u) sbs)) (Subst A sbs)
  ).
  { compsubst1 ; try eassumption.
    eapply CongTySubst ; eassumption.
  }
  assert (isterm G (subst (var 0) (sbcomp (sbzero D A u) sbs)) (Subst A sbs)).
  { eapply TermTyConv ; eassumption. }
  assert (istype D (Subst (Subst A (sbweak D A)) (sbzero D A u))).
  { eapply TySubst ; eassumption. }
  assert (istype D (Subst A (sbid D))).
  { eapply TySubst ; eassumption. }
  assert (eqtype D (Subst A (sbid D)) A).
  { eapply EqTyIdSubst ; eassumption. }
  assert (eqtype D A (Subst A (sbid D))).
  { eapply EqTySym ; eassumption. }
  assert (isterm D u (Subst A (sbid D))).
  { eapply TermTyConv ; eassumption. }
  assert (istype D (Subst A (sbcomp (sbweak D A) (sbzero D A u)))).
  { eapply TySubst ; eassumption. }
  assert (eqtype D (Subst (Subst A (sbweak D A)) (sbzero D A u)) A).
  { eapply EqTyTrans ; [
      compsubst1 ; [
        eassumption
      | eassumption
      | assumption
      | eapply CongTySubst ; [
          eapply WeakZero ; [
            assumption
          | exact H1
          | ..
          ]
        | eapply EqTyRefl
        | ..
        ]
      | ..
      ]
    | ..
    ] ; eassumption.
  }
  assert (isterm D (subst (var 0) (sbzero D A u)) A).
  { eapply TermTyConv ; [
      eapply TermSubst
    | ..
    ] ; eassumption.
  }
  assert (
    eqtype G (Subst A sbs) (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A u) sbs))
  ).
  { eapply EqTySym ; eassumption. }
  assert (
    isterm G
           (subst (subst (var 0) (sbzero D A u)) sbs)
           (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A u) sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst
    | ..
    ] ; eassumption.
  }
  assert (isterm G (subst (subst (var 0) (sbzero D A u)) sbs) (Subst A sbs)).
  { eapply TermSubst ; eassumption. }
  assert (eqsubst sbs sbs G D).
  { eapply SubstRefl ; assumption. }



  eapply EqTrans ; [
    eapply EqSym ; [
      eapply EqTyConv ; [ eapply EqSubstComp | .. ]
    | ..
    ] ; eassumption
  | eapply CongTermSubst ; [
      eassumption
    | eapply EqSubstZeroZero ; assumption
    | eassumption ..
    ]
  | assumption ..
  ].
Defined.


Ltac cando token :=
  match token with
  | true => idtac
  | false => fail "Cannot do" token
  end.


(* Some tactic to push substitutions inside one step. *)
(* Partial for now. *)
Ltac prepushsubst1 sym :=
  lazymatch goal with
  (*! Pushing in types !*)
  (* Is this first goal ever necessary? *)
  | |- eqtype ?G (Subst (Subst ?A ?sbs) ?sbt) ?B =>
    eapply EqTyTrans ; [
      eapply CongTySubst ; [
        eapply SubstRefl
      | prepushsubst1 true
      | ..
      ]
    | ..
    ]
  | |- eqtype ?G (Subst (Id ?A ?u ?v) ?sbs) ?B =>
    eapply EqTyTrans ; [ eapply EqTySubstId | .. ]
  | |- eqtype ?G (Subst ?A ?sbs) (Id ?B ?u ?v) =>
    eapply EqTyTrans ; [ eapply EqTySubstId | .. ]
  | |- eqtype ?G ?A (Subst (Id ?B ?u ?v) ?sbs) =>
    eapply EqTySym ; [
      eapply EqTyTrans ; [ eapply EqTySubstId | .. ]
    | ..
    ]
  | |- eqtype ?G (Id ?A ?u ?v) (Subst ?B) =>
    eapply EqTySym ; [
      eapply EqTyTrans ; [ eapply EqTySubstId | .. ]
    | ..
    ]
  | |- eqtype ?G (Subst (Prod ?A ?B) ?sbs) ?C =>
    eapply EqTyTrans ; [ eapply EqTySubstProd | .. ]
  | |- eqtype ?G ?A (Subst (Prod ?B ?C) ?sbs) =>
    eapply EqTySym ; [ eapply EqTyTrans ; [ eapply EqTySubstProd | .. ] | .. ]
  | |- eqtype ?G (Subst ?E ?sbs) Empty =>
    eapply EqTySubstEmpty
  | |- eqtype ?G (Subst Empty ?sbs) ?A =>
    eapply EqTyTrans ; [ eapply EqTySubstEmpty | .. ]
  | |- eqtype ?G Empty (Subst ?E ?sbs) =>
    eapply EqTySym ; [ eapply EqTySubstEmpty | .. ]
  | |- eqtype ?G ?A (Subst Empty ?sbs) =>
    eapply EqTySym ; [
      eapply EqTyTrans ; [ eapply EqTySubstEmpty | .. ]
    | ..
    ]
  | |- eqtype ?G (Subst Unit ?sbs) ?A =>
    eapply EqTyTrans ; [ eapply EqTySubstUnit | .. ]
  | |- eqtype ?G ?A (Subst Unit ?sbs) =>
    eapply EqTySym ; [
      eapply EqTyTrans ; [ eapply EqTySubstUnit | .. ]
    | ..
    ]
  | |- eqtype ?G (Subst ?A ?sbs) Bool =>
    eapply EqTySubstBool
  | |- eqtype ?G (Subst Bool ?sbs) ?A =>
    eapply EqTyTrans ; [ eapply EqTySubstBool | .. ]
  | |- eqtype ?G ?A (Subst Bool ?sbs) =>
    eapply EqTySym ; [
      eapply EqTyTrans ; [ eapply EqTySubstBool | .. ]
    | ..
    ]

  (*! Pushing in terms !*)
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    first [
      eapply EqTrans ; [ eapply EqSubstRefl | .. ]
    | eapply EqTyConv ; [
        eapply EqTrans ; [ eapply EqSubstRefl | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G (subst true ?sbs) ?u ?A =>
    first [
      eapply EqTrans ; [ eapply EqSubstTrue | .. ]
    | eapply EqTyConv ; [
        eapply EqTrans ; [ eapply EqSubstTrue | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G (subst false ?sbs) ?u ?A =>
    first [
      eapply EqTrans ; [ eapply EqSubstFalse | .. ]
    | eapply EqTyConv ; [
        eapply EqTrans ; [ eapply EqSubstFalse | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G (subst (var 0) (sbzero ?D ?B ?u)) ?v ?A =>
    first [
      eapply EqTrans ; [ eapply EqSubstZeroZero | .. ]
    | eapply EqTrans ; [
        eapply EqTyConv ; [ eapply EqSubstZeroZero | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G ?u (subst (var 0) (sbzero ?D ?B ?v)) ?A =>
    eapply EqSym ; [ eapply EqTrans ; [ eapply EqSubstZeroZero | .. ] | .. ]
  | |- eqterm ?G (subst (var 0) (sbshift ?D ?B ?sbs)) ?v ?A =>
    eapply EqTrans ; [
      eapply EqTyConv ; [
        eapply EqSubstShiftZero
      | ..
      ]
    | ..
    ]
  | |- eqterm ?G ?u (subst (var 0) (sbshift ?D ?B ?sbs)) ?A =>
    eapply EqSym ; [
      eapply EqTrans ; [
        eapply EqTyConv ; [
          eapply EqSubstShiftZero
        | ..
        ]
      | ..
      ]
    | ..
    ]
  | |- eqterm ?G (subst (var 0) (sbcomp (sbzero _ _ ?u) ?sbt)) ?v ?A =>
    first [
      eapply EqTrans ; [
        eapply EqCompZero
      | ..
      ]
    | eapply EqTrans ; [
        eapply EqTyConv ; [ eapply EqCompZero | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G (subst (var 0) (sbcomp (sbshift _ _ ?sbs) ?sbt)) ?v ?A =>
    eapply EqTrans ; [
      eapply EqTrans ; [
        eapply EqSym ; [
          eapply EqTyConv ; [ eapply EqSubstComp | .. ]
        | ..
        ]
      | eapply EqTyConv ; [
          eapply CongTermSubst ; [
            eapply SubstRefl
          | eapply EqSubstShiftZero
          | ..
          ]
        | ..
        ]
      | ..
      ]
    | ..
    ]
  (* Instead of writing all symmetry cases *)
  | |- eqterm ?G ?u ?v ?A =>
    tryif (cando sym)
    then eapply EqSym ; [ prepushsubst1 false | .. ]
    else fail "Not a goal handled by pushsubst: eqterm" G u v A
  | |- ?G => fail "Not a goal handled by pushsubst" G
  end.

Ltac pushsubst1 := prepushsubst1 true.

(* A lemma to do ZeroShift shifted, it not very robust as we would need
   some ZeroShift3 if ever we add a constructor that has three variables. *)
Lemma ZeroShift2 :
  forall {G D A B C u sbs},
    eqtype D C (Subst B (sbzero D A u)) ->
    isterm D u A ->
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    istype D C ->
    isctx G ->
    isctx D ->
    eqsubst (sbcomp (sbshift D B (sbzero D A u))
                    (sbshift G C sbs))
            (sbcomp (sbshift (ctxextend G (Subst A sbs)) B (sbshift G A sbs))
                    (sbshift G
                             (Subst B (sbshift G A sbs))
                             (sbzero G (Subst A sbs) (subst u sbs))))
            (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
            (ctxextend (ctxextend D A) B).
Proof.
  intros.
  assert (isctx (ctxextend D A)).
  { eapply CtxExtend ; assumption. }
  assert (istype D (Subst B (sbzero D A u))).
  assert (issubst (sbzero D A u) D (ctxextend D A)).
  { eapply SubstZero ; assumption. }
  { eapply TySubst ; eassumption. }
  assert (istype G (Subst C sbs)).
  { eapply TySubst ; eassumption. }
  assert (istype G (Subst (Subst B (sbzero D A u)) sbs)).
  { eapply TySubst ; eassumption. }
  assert (isctx (ctxextend D C)).
  { eapply CtxExtend ; assumption. }
  assert (isctx (ctxextend G (Subst C sbs))).
  { eapply CtxExtend ; assumption. }
  assert (isctx (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))).
  { eapply CtxExtend ; assumption. }
  assert (
    issubst (sbshift G C sbs) (ctxextend G (Subst C sbs)) (ctxextend D C)
  ).
  { eapply SubstShift ; assumption. }
  assert (eqctx G G).
  { eapply CtxRefl. assumption. }
  assert (eqtype D (Subst B (sbzero D A u)) C).
  { eapply EqTySym ; assumption. }
  assert (eqtype G (Subst (Subst B (sbzero D A u)) sbs) (Subst C sbs)).
  { eapply CongTySubst ; [
      eapply @SubstRefl with (D := D) ; assumption
    | assumption ..
    ].
  }
  assert (
    eqctx (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
    (ctxextend G (Subst C sbs))
  ).
  { eapply EqCtxExtend ; assumption. }
  assert (eqctx D D).
  { eapply CtxRefl. assumption. }
  assert (eqctx (ctxextend D (Subst B (sbzero D A u))) (ctxextend D C)).
  { eapply EqCtxExtend ; assumption. }
  assert (isctx (ctxextend D (Subst B (sbzero D A u)))).
  { eapply CtxExtend ; assumption. }
  assert (
    issubst (sbshift G (Subst B (sbzero D A u)) sbs)
            (ctxextend G (Subst C sbs))
            (ctxextend D C)
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (isctx (ctxextend (ctxextend D A) B)).
  { eapply CtxExtend ; assumption. }
  assert (issubst (sbzero D A u) D (ctxextend D A)).
  { eapply SubstZero ; assumption. }
  assert (eqctx (ctxextend (ctxextend D A) B) (ctxextend (ctxextend D A) B)).
  { apply CtxRefl. assumption. }
  assert (
    issubst (sbshift D B (sbzero D A u)) (ctxextend D C)
            (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (eqtype G (Subst C sbs) (Subst (Subst B (sbzero D A u)) sbs)).
  { eapply EqTySym ; assumption. }
  assert (
    eqctx (ctxextend G (Subst C sbs))
          (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
  ).
  { eapply EqCtxExtend ; assumption. }
  assert (eqctx (ctxextend D C) (ctxextend D C)).
  { apply CtxRefl. assumption. }
  assert (
    issubst (sbshift G C sbs)
            (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
            (ctxextend D C)
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    eqctx (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
          (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
  ).
  { eapply CtxRefl. assumption. }
  assert (
    issubst (sbshift G (Subst B (sbzero D A u)) sbs)
            (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
            (ctxextend D C)
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (issubst (sbcomp (sbzero D A u) sbs) G (ctxextend D A)).
  { eapply SubstComp ; eassumption. }
  assert (istype G (Subst B (sbcomp (sbzero D A u) sbs))).
  { eapply TySubst ; eassumption. }
  assert (
    eqtype G (Subst B (sbcomp (sbzero D A u) sbs))
           (Subst (Subst B (sbzero D A u)) sbs)
  ).
  { eapply EqTySym ; [
      eapply EqTySubstComp ; eassumption
    | assumption ..
    ].
  }
  assert (
    eqctx (ctxextend G (Subst B (sbcomp (sbzero D A u) sbs)))
          (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
  ).
  { eapply EqCtxExtend ; assumption. }
  assert (isctx (ctxextend G (Subst B (sbcomp (sbzero D A u) sbs)))).
  { eapply CtxExtend ; assumption. }
  assert (
    eqctx (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
          (ctxextend G (Subst B (sbcomp (sbzero D A u) sbs)))
  ).
  { apply CtxSym ; assumption. }
  assert (
    eqctx (ctxextend D (Subst B (sbzero D A u)))
          (ctxextend D (Subst B (sbzero D A u)))
  ).
  { apply CtxRefl. assumption. }
  assert (
    issubst (sbshift G (Subst B (sbzero D A u)) sbs)
            (ctxextend G (Subst B (sbcomp (sbzero D A u) sbs)))
            (ctxextend D (Subst B (sbzero D A u)))
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    issubst (sbshift D B (sbzero D A u)) (ctxextend D (Subst B (sbzero D A u)))
            (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstShift ; assumption. }
  assert (
    issubst
      (sbcomp (sbshift D B (sbzero D A u))
              (sbshift G (Subst B (sbzero D A u)) sbs))
      (ctxextend G (Subst B (sbcomp (sbzero D A u) sbs)))
      (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstComp ; eassumption. }
  assert (
    eqctx (ctxextend G (Subst B (sbcomp (sbzero D A u) sbs)))
          (ctxextend G (Subst B (sbcomp (sbzero D A u) sbs)))
  ).
  { eapply CtxRefl. assumption. }
  assert (
    issubst (sbshift G B (sbcomp (sbzero D A u) sbs))
            (ctxextend G (Subst B (sbcomp (sbzero D A u) sbs)))
            (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (isterm G (subst u sbs) (Subst A sbs)).
  { eapply TermSubst ; eassumption. }
  assert (istype G (Subst A sbs)).
  { eapply TySubst ; eassumption. }
  assert (
    issubst (sbzero G (Subst A sbs) (subst u sbs))
            G
            (ctxextend G (Subst A sbs))
  ).
  { eapply SubstZero ; assumption. }
  assert (
    issubst (sbshift G A sbs) (ctxextend G (Subst A sbs)) (ctxextend D A)
  ).
  { eapply SubstShift ; assumption. }
  assert (isctx (ctxextend G (Subst A sbs))).
  { eapply CtxExtend ; assumption. }
  assert (
    issubst (sbcomp (sbshift G A sbs)
                    (sbzero G (Subst A sbs) (subst u sbs))) G
            (ctxextend D A)
  ).
  { eapply SubstComp ; eassumption. }
  assert (
    istype G
           (Subst B (sbcomp (sbshift G A sbs)
                            (sbzero G (Subst A sbs) (subst u sbs))))
  ).
  { eapply TySubst ; eassumption. }
  assert (
    eqsubst (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst u sbs)))
            (sbcomp (sbzero D A u) sbs)
            G
            (ctxextend D A)
  ).
  { eapply ShiftZero ; assumption. }
  assert (eqtype (ctxextend D A) B B).
  { eapply EqTyRefl ; assumption. }
  assert (
    eqtype G
           (Subst B (sbcomp (sbshift G A sbs)
                            (sbzero G (Subst A sbs) (subst u sbs))))
           (Subst B (sbcomp (sbzero D A u) sbs))
  ).
  { eapply CongTySubst ; eassumption. }
  assert (
    eqctx
      (ctxextend G
                 (Subst B
                        (sbcomp (sbshift G A sbs)
                                (sbzero G (Subst A sbs) (subst u sbs)))))
      (ctxextend G (Subst B (sbcomp (sbzero D A u) sbs)))
  ).
  { eapply EqCtxExtend ; assumption. }
  assert (
    isctx
      (ctxextend G
                 (Subst B (sbcomp (sbshift G A sbs)
                                  (sbzero G (Subst A sbs) (subst u sbs)))))
  ).
  { eapply CtxExtend ; assumption. }
  assert (
    issubst
      (sbshift G
               B
               (sbcomp (sbshift G A sbs)
                       (sbzero G (Subst A sbs) (subst u sbs))))
      (ctxextend G (Subst B (sbcomp (sbzero D A u) sbs)))
      (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    eqtype G (Subst B (sbcomp (sbzero D A u) sbs))
    (Subst B (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst u sbs))))
  ).
  { eapply EqTySym ; assumption. }
  assert (
    eqtype G
    (Subst B (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst u sbs))))
    (Subst (Subst B (sbzero D A u)) sbs)
  ).
  { eapply EqTySym ; [
      eapply EqTyTrans ; [
        eapply EqTySubstComp ; eassumption
      | assumption ..
      ]
    | assumption ..
    ].
  }
  assert (
    eqctx
      (ctxextend G
                 (Subst B (sbcomp (sbshift G A sbs)
                                  (sbzero G (Subst A sbs) (subst u sbs)))))
      (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
  ).
  { eapply EqCtxExtend ; assumption. }
  assert (istype (ctxextend G (Subst A sbs)) (Subst B (sbshift G A sbs))).
  { eapply TySubst ; eassumption. }
  assert (
    istype G
    (Subst (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst u sbs)))
  ).
  { eapply TySubst ; eassumption. }
  assert (
    eqtype G
    (Subst (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst u sbs)))
    (Subst B (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst u sbs))))
  ).
  { eapply EqTySubstComp ; eassumption. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst u sbs))))
    (ctxextend G
       (Subst B (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst u sbs)))))
  ).
  { eapply EqCtxExtend ; assumption. }
  assert (
    isctx (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift G A sbs)))
  ).
  { eapply CtxExtend ; assumption. }
  assert (
    eqctx (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift G A sbs)))
    (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift G A sbs)))
  ).
  { eapply CtxRefl ; assumption. }
  assert (
    isctx
    (ctxextend G
       (Subst (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst u sbs))))
  ).
  { eapply CtxExtend ; assumption. }
  assert (
    issubst
    (sbshift G (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst u sbs)))
    (ctxextend G
       (Subst B (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst u sbs)))))
    (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift G A sbs)))
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    issubst (sbshift (ctxextend G (Subst A sbs)) B (sbshift G A sbs))
    (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift G A sbs)))
    (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstShift ; assumption. }
  assert (
    issubst
    (sbcomp (sbshift (ctxextend G (Subst A sbs)) B (sbshift G A sbs))
       (sbshift G (Subst B (sbshift G A sbs))
          (sbzero G (Subst A sbs) (subst u sbs))))
    (ctxextend G
       (Subst B (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst u sbs)))))
    (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstComp ; eassumption. }
  assert (
    issubst
    (sbshift G B (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst u sbs))))
    (ctxextend G
       (Subst B (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst u sbs)))))
    (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstShift ; assumption. }
  assert (
    eqtype G
    (Subst (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst u sbs)))
    (Subst (Subst B (sbzero D A u)) sbs)
  ).
  { eapply EqTyTrans ; [
      eapply EqTySubstComp ; eassumption
    | eapply EqTySym ; [
        eapply EqTyTrans ; [
          eapply EqTySubstComp ; eassumption
        | assumption ..
        ]
      | assumption ..
      ]
    | assumption ..
    ].
  }
  assert (
    eqctx
    (ctxextend G
       (Subst (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst u sbs))))
    (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
  ).
  { eapply EqCtxExtend ; assumption. }
  assert (
    issubst
    (sbshift G (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst u sbs)))
    (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
    (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift G A sbs)))
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    issubst
    (sbcomp (sbshift (ctxextend G (Subst A sbs)) B (sbshift G A sbs))
       (sbshift G (Subst B (sbshift G A sbs))
          (sbzero G (Subst A sbs) (subst u sbs))))
    (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
    (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstComp ; eassumption. }
  assert (
    issubst
    (sbshift G B (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst u sbs))))
    (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
    (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    issubst (sbshift G B (sbcomp (sbzero D A u) sbs))
    (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
    (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstCtxConv ; [
      eapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    issubst
    (sbcomp (sbshift D B (sbzero D A u)) (sbshift G (Subst B (sbzero D A u)) sbs))
    (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
    (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstComp ; eassumption. }
  assert (
    issubst (sbcomp (sbshift D B (sbzero D A u)) (sbshift G C sbs))
    (ctxextend G (Subst (Subst B (sbzero D A u)) sbs))
    (ctxextend (ctxextend D A) B)
  ).
  { eapply SubstComp ; eassumption. }




  eapply SubstTrans ; [
    eapply CongSubstComp ; [
      eapply EqSubstCtxConv ; [
        eapply CongSubstShift ; [
          eapply CtxRefl ; assumption
        | eapply @SubstRefl with (D := D) ; assumption
        | eassumption
        | assumption ..
        ]
      | eapply EqCtxExtend ; assumption
      | eapply CtxRefl ; assumption
      | assumption ..
      ]
    | eapply SubstRefl ; assumption
    | assumption ..
    ]
  | eapply SubstTrans ; [
      eapply EqSubstCtxConv ; [
        eapply @CompShift with (E := ctxextend D A) ; assumption
      | assumption ..
      ]
    | eapply SubstTrans ; [
        eapply EqSubstCtxConv ; [
          eapply CongSubstShift ; [
             eapply CtxRefl ; assumption
           | eapply SubstSym ; [
               eapply ShiftZero ; assumption
             | assumption ..
             ]
           | eapply EqTyRefl ; assumption
           | assumption ..
           ]
        | assumption ..
        ]
      | eapply SubstTrans ; [
          eapply SubstSym ; [
             eapply EqSubstCtxConv ; [
                eapply @CompShift
                 with (D := ctxextend G (Subst A sbs))
                        (E := ctxextend D A) ; assumption
              | assumption ..
              ]
           | assumption ..
           ]
        | eapply SubstRefl ; assumption
        | assumption ..
        ]
      | assumption ..
      ]
    | assumption ..
    ]
  | assumption ..
  ].
Defined.

(* A simplify tactic to simplify substitutions *)
Ltac ecomp lm :=
  eapply SubstTrans ; [
    eapply CompAssoc
  | eapply CongSubstComp ; [
      eapply SubstRefl
    | eapply lm
    | ..
    ]
  | ..
  ].

Ltac simplify_subst :=
  lazymatch goal with
  | |- eqsubst ?sbs ?sbt ?G ?D =>

      lazymatch sbs with

      | sbcomp (sbcomp ?sbs ?sbt) ?sbr =>
        eapply SubstSym ; [
          eapply CompAssoc
        | ..
        ]

      | sbcomp (sbid _) ?sbs =>
        eapply CompIdLeft

      | sbcomp ?sbs (sbid _) =>
        eapply CompIdRight

      | sbcomp (sbweak _ _) (sbzero _ _ _) =>
        eapply WeakZero
      | sbcomp (sbweak _ _) (sbcomp (sbzero _ _ _) _) =>
        ecomp WeakZero

      | sbcomp (sbweak _ _) (sbshift _ _ _) =>
        eapply WeakNat
      | sbcomp (sbweak _ _) (sbcomp (sbshift _ _ _) _) =>
        ecomp WeakNat

      | sbcomp (sbzero _ _ _) ?sbs =>
        eapply SubstSym ; [ eapply ShiftZero | .. ]

      | sbshift _ _ (sbcomp ?sbs ?sbt) =>
        eapply SubstSym ; [ eapply CompShift | .. ]
      | sbcomp (sbshift _ _ (sbcomp _ _)) _ =>
        eapply SubstTrans ; [
          eapply CompAssoc
        | eapply CongSubstComp ; [
            eapply SubstRefl
          | eapply SubstSym ; [ eapply CompShift | .. ]
          | ..
          ]
        | ..
        ]

      (* After ZeroShift, comes ZeroShift2 *)
      | sbcomp (sbshift _ _ (sbzero _ _ _)) (sbshift _ _ _) =>
        eapply ZeroShift2
      | sbcomp (sbshift _ _ (sbzero _ _ _)) (sbcomp (sbshift _ _ _) _) =>
        ecomp ZeroShift2

      | sbcomp ?sbs ?sbt =>
        eapply CongSubstComp ; [
          simplify_subst
        | eapply SubstRefl
        | ..
        ]

      | ?sbs => fail "Cannot simplify substitution" sbs

      end

  | |- ?G => fail "Cannot simplify substitution in goal" G
  end.

(* Simplify tactic *)
(* Its purpose is simplifying substitutions in equalities,
   assuming the substitution is on the left. *)
Ltac simplify :=
  lazymatch goal with
  | |- eqtype ?G (Subst ?A (sbid ?D)) ?B =>
    eapply EqTyTrans ; [
      eapply EqTyIdSubst
    | ..
    ]

  | |- eqtype ?G (Subst ?A ?sbs) ?B =>
    eapply EqTyTrans ; [
      eapply CongTySubst ; [
        simplify_subst
      | eapply EqTyRefl
      | ..
      ]
    | ..
    ]

  | |- eqterm ?G (subst ?u (sbid _)) ?v ?A =>
    eapply EqTrans ; [
      eapply EqIdSubst
    | ..
    ]

  | |- eqterm ?G (subst ?u ?sbs) ?v ?A =>
    first [
      eapply EqTrans ; [
        eapply CongTermSubst ; [
          simplify_subst
        | eapply EqRefl
        | ..
        ]
      | ..
      ]
    | eapply EqTrans ; [
        eapply EqTyConv ; [
          eapply CongTermSubst ; [
            simplify_subst
          | eapply EqRefl
          | ..
          ]
        | ..
        ]
      | ..
      ]
    ]

  | |- ?G => fail "Cannot simplify goal" G
  end.

(* Checking if we're dealing with a suitable goal. *)
(* This would be interesting in another file maybe? *)
Ltac check_goal :=
  lazymatch goal with
  | |- isctx ?G => idtac
  | |- issubst ?sbs ?G ?D => idtac
  | |- istype ?G ?A => idtac
  | |- isterm ?G ?u ?A => idtac
  | |- eqctx ?G ?D => idtac
  | |- eqsubst ?sbs ?sbt ?G ?D => idtac
  | |- eqtype ?G ?A ?B => idtac
  | |- eqterm ?G ?u ?v ?A => idtac
  | |- ?G => fail "Goal" G " is not a goal meant to be handled by magic."
  end.

(* My own tactic to fail with the goal information. *)
Ltac myfail debug :=
  lazymatch goal with
  | |- ?G =>
    tryif (cando debug)
    then fail 1000 "Cannot solve subgoal" G
    else fail "Cannot solve subgoal" G
  | _ => fail "This shouldn't happen!"
  end.

(* Factorizing some cases *)
Ltac eqtype_subst G A sbs B k try shelf tysym debug :=
  tryif (is_var A)
  then (
    tryif (is_var sbs)
    then (
      match B with
      | Subst ?B ?sbt =>
        tryif (is_var B)
        then (
          tryif (is_var sbt)
          then first [
            eapply CongTySubst
          | myfail debug
          ] ; k try shelf true debug
          else first [
            eapply EqTySym ; [ simplify | .. ]
          | eapply CongTySubst
          | myfail debug
          ] ; k try shelf true debug
        )
        else first [
          pushsubst1
        | myfail debug
        ] ; k try shelf true debug
      | _ =>
        first [
          eapply CongTySubst
        | myfail debug
        ] ; k try shelf true debug
      end
    )
    else
      match B with
      | Subst ?B ?sbt =>
        tryif (is_var B)
        then (
          tryif (is_var sbt)
          then first [
            simplify
          | eapply CongTySubst
          | myfail debug
          ] ; k try shelf true debug
          else first [
            simplify
          | eapply EqTySym ; [ simplify | .. ]
          | eapply CongTySubst
          | myfail debug
          ] ; k try shelf true debug
        )
        else first [
          (* Should we simplify on the left first? *)
          pushsubst1
        | simplify
        | cando tysym ; eapply EqTySym ; [ simplify | .. ]
        | myfail debug
        ] ; k try shelf true debug
      | _ =>
        first [
          simplify
        | eapply CongTySubst
        | myfail debug
        ] ; k try shelf true debug
      end
  )
  else first [
    pushsubst1
  | cando tysym ; eapply EqTySym ; [ simplify | .. ]
  | myfail debug
  ] ; k try shelf true debug.

(* Magic Tactic *)
(* It is basically a type checker that doesn't do the smart things,
   namely type and context conversions (and it doesn't rely on reflection
   obviously). *)
Ltac magicn try shelf tysym debug :=
  (* We only ever apply magic to suitable goals *)
  check_goal ;
  first [
    assumption (* Why can't I remove it? *)
  | (* We have several things we need to do to the tactic:
       * Remove the _ case.
       * Add a token to solve equalities with only one side as reflexivity.
         (Maybe shelve them in the meantime?)
       * We can take advantage of the information we have at hand on
         substitutions to make magic finer!
     *)
    lazymatch goal with
    (*! Contexts !*)
    | |- isctx ctxempty =>
      apply CtxEmpty
    | |- isctx (ctxextend ?G ?A) =>
      eapply CtxExtend ; magicn try shelf true debug
    | |- isctx ?G =>
      tryif (is_var G)
      then first [
        assumption
      | myfail debug
      ]
      else tryif (cando shelf)
        then shelve
        else myfail debug

    (*! Substitutions !*)
    | |- issubst (sbzero _ _ ?u) ?G1 ?G2 =>
      first [
        eapply SubstZero
      | eapply SubstCtxConv ; [ eapply SubstZero | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- issubst (sbweak _ _) ?G1 ?G2 =>
      first [
        eapply SubstWeak
      | eapply SubstCtxConv ; [ eapply SubstWeak | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- issubst (sbshift _ _ ?sbs) ?G1 ?G2 =>
      first [
        eapply SubstShift
      | eapply SubstCtxConv ; [ eapply SubstShift | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- issubst (sbid _) ?G1 ?G2 =>
      first [
        eapply SubstId
      | myfail debug
      ] ; magicn try shelf true debug
    | |- issubst (sbcomp ?sbt ?sbs) ?G1 ?G2 =>
      first [
        eapply SubstComp
      | myfail debug
      ] ; magicn try shelf true debug
    | |- issubst ?sbs ?G1 ?G2 =>
      tryif (is_var sbs) then (
        first [
          eassumption
        | eapply SubstCtxConv
        | myfail debug
        ] ; magicn try shelf tysym debug
      )
      else tryif (cando shelf)
        then shelve
        else myfail debug

    (*! Types !*)
    | |- istype ?G (Subst ?A ?sbs) =>
      first [
        eapply TySubst
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G (Prod ?A ?B) =>
      first [
        eapply TyProd
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G (Id ?A ?u ?v) =>
      first [
        eapply TyId
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G Empty =>
      first [
        eapply TyEmpty
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G Unit =>
      first [
        eapply TyUnit
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G Bool =>
      first [
        eapply TyBool
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G ?A =>
      tryif (is_var A)
      then first [
        eassumption
      | eapply TyCtxConv ; [ eassumption | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
      else tryif (cando shelf)
        then shelve
        else myfail debug

    (*! Terms !*)
    | |- isterm ?G (subst ?u ?sbs) ?A =>
      first [
        eapply TermSubst
      | eapply TermTyConv ; [
          eapply TermSubst
        | ..
        ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm (ctxextend ?G ?A) (var 0) ?T =>
      first [
        eapply TermVarZero
      | eapply TermTyConv ; [ eapply TermVarZero | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm (ctxextend ?G ?B) (var (S ?k)) ?A =>
      first [
        eapply TermVarSucc
      | eapply TermTyConv ; [ eapply TermVarSucc | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (var ?k) ?A =>
      (* In that case, we might shelve, if the don't know the context. *)
      tryif (is_evar G)
      then shelve
      else first [
        eassumption
      | myfail debug
      ]
    | |- isterm ?G (lam ?A ?B ?u) ?C =>
      first [
        eapply TermAbs
      | eapply TermTyConv ; [ eapply TermAbs | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (app ?u ?A ?B ?v) ?C =>
      first [
        eapply TermApp
      | eapply TermTyConv ; [ eapply TermApp | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (refl ?A ?u) ?B =>
      first [
        eapply TermRefl
      | eapply TermTyConv ; [ eapply TermRefl | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (j ?A ?u ?C ?w ?v ?p) ?T =>
      first [
        eapply TermJ
      | eapply TermTyConv ; [ eapply TermJ | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (exfalso ?A ?u) _ =>
      first [
        eapply TermExfalso
      | eapply TermTyConv ; [ eapply TermExfalso | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G unit ?A =>
      first [
        eapply TermUnit
      | eapply TermTyConv ; [ eapply TermUnit | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G true ?A =>
      first [
        eapply TermTrue
      | eapply TermTyConv ; [ eapply TermTrue | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G false ?A =>
      first [
        eapply TermFalse
      | eapply TermTyConv ; [ eapply TermFalse | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (cond ?C ?u ?v ?w) ?T =>
      first [
        eapply TermCond
      | eapply TermTyConv ; [ eapply TermCond | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | [ H : isterm ?G ?v ?A, H' : isterm ?G ?v ?B |- isterm ?G ?v ?C ] =>
      (* We have several options so we don't take any risk. *)
      (* Eventually this should go away. I don't want to do the assert thing
         anymore. *)
      first [
        is_var A ; exact H
      | is_var B ; exact H'
      | cando shelf ; shelve
      ]
    | |- isterm ?G ?u ?A =>
      tryif (is_evar u)
      (* If u is an existential variable we don't touch it. *)
      then tryif (cando shelf)
        then shelve
        else myfail debug
      else (
        tryif (is_var u)
        then first [
          eassumption
        | eapply TermTyConv ; [ eassumption | .. ]
        | eapply TermCtxConv ; [ eassumption | .. ]
        | eapply TermCtxConv ; [
            eapply TermTyConv ; [ eassumption | .. ]
          | ..
          ]
        | myfail debug
        ] ; magicn try shelf true debug
        else tryif (cando shelf)
          then shelve
          else myfail debug
      )

    (*! Equality of contexts !*)
    | |- eqctx ctxempty ctxempty =>
      apply EqCtxEmpty
    | |- eqctx (ctxextend ?G ?A) (ctxextend ?D ?B) =>
      first [
        eapply EqCtxExtend
      | apply CtxSym ; [ eapply EqCtxExtend | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqctx ?G ?G =>
      first [
        eapply CtxRefl
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqctx ?G ?D =>
      tryif (is_var G ; is_var D)
      then first [
        assumption
      | apply CtxSym ; [ assumption | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
      else tryif (cando shelf)
        then shelve
        else myfail debug

    (*! Equality of substitutions !*)
    | |- eqsubst (sbcomp (sbweak _ _) (sbshift _ _ ?sbs))
                (sbcomp ?sbs (sbweak _ _)) ?G ?D =>
      first [
        eapply WeakNat
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqsubst (sbcomp ?sbs (sbweak _ _))
                (sbcomp (sbweak _ _) (sbshift _ _ ?sbs)) ?G ?D =>
      first [
        eapply SubstSym ; [ eapply WeakNat | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqsubst (sbzero _ _ ?u1) (sbzero _ _ ?u2) ?D ?E =>
      first [
        eapply CongSubstZero
      | eapply EqSubstCtxConv ; [ eapply CongSubstZero | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqsubst (sbweak _ _) (sbweak _ _) ?D ?E =>
      first [
        eapply CongSubstWeak
      | eapply EqSubstCtxConv ; [ eapply CongSubstWeak | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqsubst (sbshift _ _ ?sbs1) (sbshift _ _ ?sbs2) ?D ?E =>
      first [
        eapply CongSubstShift
      | eapply EqSubstCtxConv ; [ eapply CongSubstShift | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqsubst ?sbs ?sbs ?G ?D =>
      first [
          eapply SubstRefl
        | myfail debug
        ] ; magicn try shelf true debug
    (* In case we have syntactically equal substitutions involved,
       we can make a little shortcut. *)
    (* | |- eqsubst (sbcomp ?sbs _) (sbcomp ?sbs _) _ _ => *)
    (*   first [ *)
    (*     eapply CongSubstComp ; [ *)
    (*       idtac *)
    (*     | eapply SubstRefl *)
    (*     | .. *)
    (*     ] *)
    (*   | myfail debug *)
    (*   ] ; magicn try shelf true debug *)
    (* | |- eqsubst (sbcomp _ ?sbs) (sbcomp _ ?sbs) _ _ => *)
    (*   first [ *)
    (*     eapply CongSubstComp ; [ *)
    (*       eapply SubstRefl *)
    (*     | .. *)
    (*     ] *)
    (*   | myfail debug *)
    (*   ] ; magicn try shelf true debug *)
    (* We need to simplify if we are ever going to apply congruence for
       composition. *)
    | |- eqsubst ?sbs ?sbt ?G ?D =>
      tryif (is_var sbs ; is_var sbt)
      then first [
        eassumption
      | eapply SubstSym ; [ eassumption | .. ]
      | eapply EqSubstCtxConv ; [ eassumption | .. ]
      | eapply SubstSym ; [
          eapply EqSubstCtxConv ; [ eassumption | .. ]
        | ..
        ]
      | myfail debug
      ] ; magicn try shelf true debug
      else first [
        eapply SubstTrans ; [ simplify_subst | .. ]
      | eapply SubstSym ; [ eapply SubstTrans ; [ simplify_subst | .. ] | .. ]
      | eapply CongSubstComp
      | myfail debug
      ] ; magicn try shelf true debug

    (*! Equality of types !*)
    | |- eqtype ?G (Subst (Subst ?A ?sbs) ?sbt) ?B =>
      first [
        compsubst1
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqtype ?G ?A (Subst (Subst ?B ?sbs) ?sbt) =>
      first [
        compsubst1
      | myfail debug
      ] ; magicn try shelf true debug
    (* A weird case perhaps. *)
    | |- eqtype ?G (Subst ?A (sbshift ?G2 ?A2 ?sbs))
               (Subst ?B' (sbcomp ?sbs (sbweak ?G1 (Subst ?A1 ?sbs)))) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := (Subst B' (sbweak _ _)))
        | myfail debug
        ] ; magicn try shelf true debug
      )
      else eqtype_subst G A (sbshift G2 A2 sbs)
                        (Subst B' (sbcomp sbs (sbweak G1 (Subst A1 sbs))))
                        magicn try shelf tysym debug
    | |- eqtype ?G (Subst ?B' (sbcomp ?sbs (sbweak ?G1 (Subst ?A1 ?sbs))))
               (Subst ?A (sbshift ?G2 ?A2 ?sbs)) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := Subst B' (sbweak _ _))
        | myfail debug
        ] ; magicn try shelf true debug
      )
      else eqtype_subst G (Subst B' (sbcomp sbs (sbweak A1 sbs)))
                        (Subst A (sbshift G2 A2 sbs))
                        magicn try shelf tysym debug
    | |- eqtype ?G
               (Subst ?A
                      (sbcomp (sbshift ?G1 ?A1 ?sbs)
                              (sbzero ?G2 ?A2 (subst ?u ?sbs))))
               (Subst ?B' ?sbs) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := Subst B' (sbweak _ _))
        | myfail debug
        ] ; magicn try shelf true debug
      )
      else eqtype_subst G
                        A
                        (sbcomp (sbshift G1 A1 sbs)
                                (sbzero G2 A2 (subst u sbs)))
                        (Subst B' sbs)
                        magicn try shelf tysym debug
    | |- eqtype ?G (Subst ?B' ?sbs)
               (Subst ?A (sbcomp (sbshift ?G1 ?A1 ?sbs)
                                 (sbzero ?G2 ?A2 (subst ?u ?sbs)))) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := Subst B' (sbweak _ _))
        | myfail debug
        ] ; magicn try shelf true debug
      )
      else eqtype_subst G B' sbs
                        (Subst A (sbcomp (sbshift G1 A1 sbs)
                                         (sbzero G2 A2 (subst u sbs))))
                        magicn try shelf tysym debug
    (* Another case I'm not sure of. *)
    | |- eqtype ?G
               (Subst ?A ?sbs)
               (Subst ?B (sbzero ?D (Subst ?A ?sbs) (subst ?u ?sbs))) =>
      tryif (is_var A ; is_evar B)
      then
        first [
          instantiate (1 := Subst (Subst A sbs) (sbweak _ _))
        | myfail debug
        ] ; magicn try shelf true debug
      else
        eqtype_subst G A sbs (Subst B (sbzero D (Subst A sbs) (subst u sbs)))
                     magicn try shelf tysym debug
    (* One more *)
    | |- eqtype ?G (Subst ?A (sbzero ?D ?B' ?u)) ?B =>
      tryif (is_evar A ; is_var B)
      then first [
        instantiate (1 := Subst B (sbweak _ _))
      | myfail debug
      ] ; magicn try shelf true debug
      else eqtype_subst G A (sbzero D B u) B
                        magicn try shelf tysym debug
    | |- eqtype ?G (Subst ?A ?sbs) (Subst ?A ?sbt) =>
      (* A little shortcut in that case. *)
      eapply CongTySubst ; [
        idtac
      | eapply EqTyRefl
      | ..
      ] ; magicn try shelf true debug
    | |- eqtype ?G (Subst ?A ?sbs) ?B =>
      (* We should push only if it makes sense. *)
      eqtype_subst G A sbs B magicn try shelf tysym debug
    | |- eqtype ?G ?A (Subst ?B ?sbs) =>
      (* We know how to deal with the symmetric case. *)
      tryif (cando tysym)
      then eapply EqTySym ; [
        magicn try shelf false debug
      | magicn try shelf true debug ..
      ]
      else myfail debug
    | |- eqtype ?G (Id ?A ?u ?v) (Id ?B ?w ?z) =>
      first [
        eapply CongId
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqtype ?G (Prod ?A ?B) (Prod ?C ?D) =>
      first [
        eapply CongProd
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqtype ?G Unit Unit =>
      first [
        eapply EqTyRefl
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqtype ?G Bool Bool =>
      first [
        eapply EqTyRefl
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqtype ?G ?A ?B =>
      tryif (is_var A ; is_var B)
      then (
        first [
          eassumption
        | eapply EqTyRefl
        | eapply EqTySym ; [ eassumption | .. ]
        | eapply EqTyCtxConv ; [
            first [
              eassumption
            | eapply EqTySym ; [ eassumption | .. ]
            ]
          | ..
          ]
        | myfail debug
        ] ; magicn try shelf true debug
      )
      else tryif (is_evar A || is_evar B)
        then tryif (cando shelf)
          then shelve
          else myfail debug
        else myfail debug

    (*! Equality of terms !*)
    | |- eqterm ?G (subst (subst ?u ?sbs) ?sbt) ?v ?A =>
      first [
        compsubst1
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G ?u (subst (subst ?v ?sbs) ?sbt) ?A =>
      first [
        compsubst1
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G (subst ?u ?sbs) ?v ?A =>
      (* Maybe some type conversion somewhere. *)
      tryif (is_var u)
      then (
        tryif (is_var sbs)
        then (
          match v with
          | subst ?v ?sbt =>
            tryif (is_var v)
            then (
              tryif (is_var sbt)
              then first [
                eapply CongTermSubst
              | eapply EqTyConv ; [
                  eapply CongTermSubst
                | ..
                ]
              | eassumption
              | myfail debug
              ] ; magicn try shelf true debug
              else first [
                eapply EqSym ; [ simplify | .. ]
              | eapply CongTermSubst
              | eapply EqTyConv ; [
                  eapply CongTermSubst
                | ..
                ]
              | myfail debug
              ] ; magicn try shelf true debug
            )
            else first [
              pushsubst1
            | eapply EqSym ; [ pushsubst1 | .. ]
            | cando shelf ; shelve
            ] ; magicn try shelf true debug
          | _ =>
            first [
              eapply CongTermSubst
            | eapply EqTyConv ; [
              eapply CongTermSubst
              | ..
              ]
            | eassumption
            | myfail debug
            ] ; magicn try shelf true debug
          end
        )
        else (
          lazymatch v with
          | subst ?v ?sbt =>
            tryif (is_var v)
            then first [
                simplify
              | eapply CongTermSubst
              | eapply EqTyConv ; [ eapply CongTermSubst | .. ]
              | myfail debug
              ] ; magicn try shelf true debug
            else first [
              pushsubst1
            | cando shelf ; shelve
            ] ; magicn try shelf true debug

          | ?v =>
            tryif (is_evar v ; cando shelf)
            then shelve
            else first [
              simplify
            | myfail debug
            ] ; magicn try shelf true debug
          end
        )
      )
      else first [
        pushsubst1
      | cando shelf ; shelve
      ] ; magicn try shelf true debug
    | |- eqterm ?G ?u (subst ?v ?sbs) ?A =>
      (* We know how to deal with the symmetric case. *)
      tryif (cando tysym)
      then eapply EqSym ; [
        magicn try shelf false debug
      | magicn try shelf true debug ..
      ]
      else myfail debug
    | |- eqterm ?G ?u ?u ?A =>
      first [
        eapply EqRefl
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G ?u ?v Empty =>
      first [
        eapply @EqTermExfalso with (w := u)
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G ?u ?v Unit =>
      first [
        eapply UnitEta
      | myfail debug
      ] ; magicn try shelf true debug
    (* Where should ProdBeta be handled? *)
    (* Same for CondTrue, CondFalse, JRefl *)
    (* ProdEta should come in after CongApp and CongProd probably *)
    | |- eqterm ?G (lam ?A1 ?A2 ?u1) (lam ?B1 ?B2 ?u2) _ =>
      first [
        eapply CongAbs
      | eapply EqTyConv ; [ eapply CongAbs | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G (app ?u1 ?A1 ?A2 ?u2) (app ?v1 ?B1 ?B2 ?v2) _ =>
      first [
        eapply CongApp
      | eapply EqTyConv ; [ eapply CongApp | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G (refl ?A1 ?u1) (refl ?A2 ?u2) _ =>
      first [
        eapply CongRefl
      | eapply EqTyConv ; [ eapply CongRefl | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G (j ?A1 ?u1 ?C1 ?w1 ?v1 ?p1) (j ?A2 ?u2 ?C2 ?w2 ?v2 ?p2) _ =>
      first [
        eapply CongJ
      | eapply EqTyConv ; [ eapply CongJ | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G (cond ?C1 ?u1 ?v1 ?w1) (cond ?C2 ?u2 ?v2 ?w2) _ =>
      first [
        eapply CongCond
      | eapply EqTyConv ; [ eapply CongCond | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G ?u ?v ?A =>
      tryif (is_var u ; is_var v)
      then first [
        eassumption
      | eapply EqRefl
      | eapply EqSym ; [ eassumption |.. ]
      | eapply EqTyConv ; [ eassumption | .. ]
      | eapply EqTyConv ; [
          eapply EqSym ; [ eassumption | .. ]
        | ..
        ]
      | myfail debug
      ] ; magicn try shelf true debug
      else tryif (is_evar u + is_evar v)
        then tryif (cando shelf)
          then shelve
          else myfail debug
        else myfail debug

    | _ => myfail debug
    end
  | cando try
  ].

Ltac magic := magicn false true true true.
Ltac okmagic := magicn false true true false.
Ltac trymagic := magicn true true true false.
Ltac strictmagic := magicn false false true true.

(* With it we improve compsubst1 *)
Ltac gocompsubst := compsubst1 ; try okmagic.

(* With it we improve pushsubst1 *)
Ltac gopushsubst := pushsubst1 ; try okmagic.

(* Tactic to keep equalities *)
Ltac keep_eq :=
  match goal with
  | |- eqterm _ _ _ _ => idtac
  | |- eqtype _ _ _ => idtac
  | |- eqsubst _ _ _ _ => idtac
  | |- eqctx _ _ => idtac
  | _ => shelve
  end.
