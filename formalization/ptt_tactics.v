(* Tactics and auxiliary lemmas for ptt. *)

Require config.
Require Import config_tactics.
Require Import tt.
Require Import syntax.

(* Work with precond. *)
Local Instance hasPrecond : config.Precond := {| config.precondFlag := config.Yes |}.

(* Some tactic to compose substitutions. *)
Lemma eqtype_subst_left `{config.Reflection} :
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
  ceapply EqTyTrans ; [
    ceapply EqTySubstComp ; eassumption
  | try assumption ..
  ].
  - ceapply TySubst ; try eassumption.
    ceapply TySubst ; eassumption.
  - ceapply TySubst ; try eassumption.
    ceapply SubstComp ; eassumption.
Defined.

Lemma eqterm_subst_left `{config.Reflection} :
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
  { ceapply TySubst ; try eassumption.
    ceapply TySubst ; eassumption. }
  assert (istype G (Subst A (sbcomp sbt sbs))).
  { ceapply TySubst ; try eassumption.
    ceapply SubstComp ; eassumption. }
  assert (isterm G (subst (subst u sbt) sbs) (Subst A (sbcomp sbt sbs))).
  { ceapply TermTyConv.
    - ceapply TermSubst ; try eassumption.
      + ceapply TermSubst ; eassumption.
      + ceapply TySubst ; eassumption.
    - ceapply eqtype_subst_left ; try eassumption.
      ceapply EqTyRefl ; eassumption.
    - assumption.
    - assumption.
    - assumption.
  }
  assert (isterm G (subst u (sbcomp sbt sbs)) (Subst A (sbcomp sbt sbs))).
  { ceapply TermSubst ; try eassumption.
    ceapply SubstComp ; eassumption.
  }

  assert (hh : eqtype G (Subst A (sbcomp sbt sbs)) (Subst (Subst A sbt) sbs)).
  { capply EqTySym ; [
      ceapply EqTySubstComp ; eassumption
    | assumption ..
    ].
  }
  assert (h : eqterm G (subst u (sbcomp sbt sbs)) v (Subst (Subst A sbt) sbs)).
  { ceapply EqTyConv ; eassumption. }
  ceapply EqTrans.
  - ceapply EqTyConv.
    + ceapply EqSubstComp ; eassumption.
    + capply EqTySym ; [
        ceapply EqTySubstComp ; eassumption
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
  - ceapply TermTyConv ; eassumption.
  - ceapply TermTyConv ; eassumption.
  - ceapply TermTyConv ; eassumption.
Defined.

Ltac compsubst1 :=
  doConfig ;
  lazymatch goal with
  | |- eqtype ?G (Subst (Subst ?A ?sbt) ?sbs) ?B =>
    ceapply eqtype_subst_left
  | |- eqtype ?G ?A (Subst (Subst ?B ?sbt) ?sbs) =>
    ceapply EqTySym ; [ ceapply eqtype_subst_left | .. ]
  | |- eqterm ?G (subst (subst ?u ?sbt) ?sbs) ?v (Subst (Subst ?A ?sbt) ?sbs) =>
    ceapply eqterm_subst_left
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) (Subst (Subst ?A ?sbt) ?sbs) =>
    ceapply EqSym ; [ ceapply eqterm_subst_left | .. ]
  | |- eqterm ?G (subst (subst ?u ?sbt) ?sbs) ?v ?A =>
    ceapply EqTyConv ; [ ceapply eqterm_subst_left | .. ]
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) ?A =>
    ceapply EqSym ; [
      ceapply EqTyConv ; [ ceapply eqterm_subst_left | .. ]
    | ..
    ]
  | |- ?G => fail "Not a goal handled by compsubst" G
  end.

Lemma EqCompZero `{config.Reflection} :
  forall {G D A u sbs},
    issubst sbs G D ->
    isterm D u A ->
    istype D A ->
    isctx G ->
    isctx D ->
    eqterm G
           (subst (var 0) (sbcomp (sbzero A u) sbs))
           (subst u sbs)
           (Subst A sbs).
Proof.
  intros.
  assert (istype G (Subst A sbs)).
  { ceapply TySubst ; eassumption. }
  assert (isterm G (subst u sbs) (Subst A sbs)).
  { ceapply TermSubst ; eassumption. }
  assert (issubst (sbzero A u) D (ctxextend D A)).
  { (config ceapply SubstZero) ; eassumption. }
  assert (isctx (ctxextend D A)).
  { ceapply CtxExtend ; assumption. }
  assert (issubst (sbcomp (sbzero A u) sbs) G (ctxextend D A)).
  { ceapply SubstComp ; eassumption. }
  assert (isterm (ctxextend D A) (var 0) (Subst A (sbweak A))).
  { capply TermVarZero ; assumption. }
  assert (issubst (sbweak A) (ctxextend D A) D).
  { ceapply SubstWeak ; assumption. }
  assert (istype (ctxextend D A) (Subst A (sbweak A))).
  { ceapply TySubst ; eassumption. }
  assert (
    isterm G
           (subst (var 0) (sbcomp (sbzero A u) sbs))
           (Subst (Subst A (sbweak A)) (sbcomp (sbzero A u) sbs))
  ).
  { ceapply TermSubst ; eassumption. }
  assert (istype G (Subst (Subst A (sbweak A)) (sbcomp (sbzero A u) sbs))).
  { ceapply TySubst ; eassumption. }
  assert (issubst (sbcomp (sbweak A) (sbcomp (sbzero A u) sbs)) G D).
  { ceapply SubstComp ; eassumption. }
  assert (istype G (Subst A (sbcomp (sbweak A) (sbcomp (sbzero A u) sbs)))).
  { ceapply TySubst ; eassumption. }
  assert (issubst (sbcomp (sbweak A) (sbzero A u)) D D).
  { ceapply SubstComp ; eassumption. }
  assert (issubst sbid D D).
  { capply SubstId. assumption. }
  assert (issubst (sbcomp (sbcomp (sbweak A) (sbzero A u)) sbs) G D).
  { ceapply SubstComp ; eassumption. }
  assert (issubst (sbcomp sbid sbs) G D).
  { ceapply SubstComp ; eassumption. }
  assert (eqsubst (sbcomp (sbweak A) (sbcomp (sbzero A u) sbs)) sbs G D).
  { ceapply SubstTrans ; [
      ceapply CompAssoc
    | ceapply SubstTrans ; [
        ceapply CongSubstComp ; [
          ceapply SubstRefl
        | ceapply WeakZero
        | ..
        ]
      | ceapply CompIdLeft
      | ..
      ]
    | ..
    ] ; eassumption.
  }
  assert (eqtype D A A).
  { ceapply EqTyRefl ; assumption. }
  assert (
    eqtype G (Subst (Subst A (sbweak A)) (sbcomp (sbzero A u) sbs)) (Subst A sbs)
  ).
  { compsubst1 ; try eassumption.
    ceapply CongTySubst ; eassumption.
  }
  assert (isterm G (subst (var 0) (sbcomp (sbzero A u) sbs)) (Subst A sbs)).
  { ceapply TermTyConv ; eassumption. }
  assert (istype D (Subst (Subst A (sbweak A)) (sbzero A u))).
  { ceapply TySubst ; eassumption. }
  assert (istype D (Subst A sbid)).
  { ceapply TySubst ; eassumption. }
  assert (eqtype D (Subst A sbid) A).
  { ceapply EqTyIdSubst ; eassumption. }
  assert (eqtype D A (Subst A sbid)).
  { ceapply EqTySym ; eassumption. }
  assert (isterm D u (Subst A sbid)).
  { ceapply TermTyConv ; eassumption. }
  assert (istype D (Subst A (sbcomp (sbweak A) (sbzero A u)))).
  { ceapply TySubst ; eassumption. }
  assert (eqtype D (Subst (Subst A (sbweak A)) (sbzero A u)) A).
  { ceapply EqTyTrans ; [
      compsubst1 ; [
        eassumption
      | eassumption
      | assumption
      | ceapply CongTySubst ; [
          ceapply WeakZero ; [
            assumption
          | ..
          ]
        | ceapply EqTyRefl
        | ..
        ]
      | ..
      ]
    | ..
    ] ; eassumption.
  }
  assert (isterm D (subst (var 0) (sbzero A u)) A).
  { ceapply TermTyConv ; [
      ceapply TermSubst
    | ..
    ] ; eassumption.
  }
  assert (
    eqtype G (Subst A sbs) (Subst (Subst A (sbweak A)) (sbcomp (sbzero A u) sbs))
  ).
  { ceapply EqTySym ; eassumption. }
  assert (
    isterm G
           (subst (subst (var 0) (sbzero A u)) sbs)
           (Subst (Subst A (sbweak A)) (sbcomp (sbzero A u) sbs))
  ).
  { ceapply TermTyConv ; [
      ceapply TermSubst
    | ..
    ] ; eassumption.
  }
  assert (isterm G (subst (subst (var 0) (sbzero A u)) sbs) (Subst A sbs)).
  { ceapply TermSubst ; eassumption. }
  assert (eqsubst sbs sbs G D).
  { ceapply SubstRefl ; assumption. }

  ceapply EqTrans ; [
    ceapply EqSym ; [
      ceapply EqTyConv ; [ ceapply EqSubstComp | .. ]
    | ..
    ] ; eassumption
  | ceapply CongTermSubst ; [
      eassumption
    | ceapply EqSubstZeroZero ; assumption
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
  doConfig ;
  lazymatch goal with
  (*! Pushing in types !*)
  (* Is this first goal ever necessary? *)
  | |- eqtype ?G (Subst (Subst ?A ?sbs) ?sbt) ?B =>
    ceapply EqTyTrans ; [
      ceapply CongTySubst ; [
        ceapply SubstRefl
      | prepushsubst1 true
      | ..
      ]
    | ..
    ]
  | |- eqtype ?G (Subst (Id ?A ?u ?v) ?sbs) ?B =>
    ceapply EqTyTrans ; [ ceapply EqTySubstId | .. ]
  | |- eqtype ?G (Subst ?A ?sbs) (Id ?B ?u ?v) =>
    ceapply EqTyTrans ; [ ceapply EqTySubstId | .. ]
  | |- eqtype ?G ?A (Subst (Id ?B ?u ?v) ?sbs) =>
    ceapply EqTySym ; [
      ceapply EqTyTrans ; [ ceapply EqTySubstId | .. ]
    | ..
    ]
  | |- eqtype ?G (Id ?A ?u ?v) (Subst ?B) =>
    ceapply EqTySym ; [
      ceapply EqTyTrans ; [ ceapply EqTySubstId | .. ]
    | ..
    ]
  | |- eqtype ?G (Subst (Prod ?A ?B) ?sbs) ?C =>
    ceapply EqTyTrans ; [ ceapply EqTySubstProd | .. ]
  | |- eqtype ?G ?A (Subst (Prod ?B ?C) ?sbs) =>
    ceapply EqTySym ; [ ceapply EqTyTrans ; [ ceapply EqTySubstProd | .. ] | .. ]
  | |- eqtype ?G (Subst ?E ?sbs) Empty =>
    ceapply EqTySubstEmpty
  | |- eqtype ?G (Subst Empty ?sbs) ?A =>
    ceapply EqTyTrans ; [ ceapply EqTySubstEmpty | .. ]
  | |- eqtype ?G Empty (Subst ?E ?sbs) =>
    ceapply EqTySym ; [ ceapply EqTySubstEmpty | .. ]
  | |- eqtype ?G ?A (Subst Empty ?sbs) =>
    ceapply EqTySym ; [
      ceapply EqTyTrans ; [ ceapply EqTySubstEmpty | .. ]
    | ..
    ]
  | |- eqtype ?G (Subst Unit ?sbs) ?A =>
    ceapply EqTyTrans ; [ ceapply EqTySubstUnit | .. ]
  | |- eqtype ?G ?A (Subst Unit ?sbs) =>
    ceapply EqTySym ; [
      ceapply EqTyTrans ; [ ceapply EqTySubstUnit | .. ]
    | ..
    ]
  | |- eqtype ?G (Subst ?A ?sbs) Bool =>
    ceapply EqTySubstBool
  | |- eqtype ?G (Subst Bool ?sbs) ?A =>
    ceapply EqTyTrans ; [ ceapply EqTySubstBool | .. ]
  | |- eqtype ?G ?A (Subst Bool ?sbs) =>
    ceapply EqTySym ; [
      ceapply EqTyTrans ; [ ceapply EqTySubstBool | .. ]
    | ..
    ]

  (*! Pushing in terms !*)
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    first [
      ceapply EqTrans ; [ ceapply EqSubstRefl | .. ]
    | ceapply EqTyConv ; [
        ceapply EqTrans ; [ ceapply EqSubstRefl | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G (subst true ?sbs) ?u ?A =>
    first [
      ceapply EqTrans ; [ ceapply EqSubstTrue | .. ]
    | ceapply EqTyConv ; [
        ceapply EqTrans ; [ ceapply EqSubstTrue | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G (subst false ?sbs) ?u ?A =>
    first [
      ceapply EqTrans ; [ ceapply EqSubstFalse | .. ]
    | ceapply EqTyConv ; [
        ceapply EqTrans ; [ ceapply EqSubstFalse | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G (subst (var 0) (sbzero ?B ?u)) ?v ?A =>
    first [
      ceapply EqTrans ; [ ceapply EqSubstZeroZero | .. ]
    | ceapply EqTrans ; [
        ceapply EqTyConv ; [ ceapply EqSubstZeroZero | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G ?u (subst (var 0) (sbzero ?B ?v)) ?A =>
    ceapply EqSym ; [ ceapply EqTrans ; [ ceapply EqSubstZeroZero | .. ] | .. ]
  | |- eqterm ?G (subst (var 0) (sbshift ?B ?sbs)) ?v ?A =>
    ceapply EqTrans ; [
      ceapply EqTyConv ; [
        ceapply EqSubstShiftZero
      | ..
      ]
    | ..
    ]
  | |- eqterm ?G ?u (subst (var 0) (sbshift ?B ?sbs)) ?A =>
    ceapply EqSym ; [
      ceapply EqTrans ; [
        ceapply EqTyConv ; [
          ceapply EqSubstShiftZero
        | ..
        ]
      | ..
      ]
    | ..
    ]
  | |- eqterm ?G (subst (var 0) (sbcomp (sbzero _ ?u) ?sbt)) ?v ?A =>
    first [
      ceapply EqTrans ; [
        ceapply EqCompZero
      | ..
      ]
    | ceapply EqTrans ; [
        ceapply EqTyConv ; [ ceapply EqCompZero | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G (subst (var 0) (sbcomp (sbshift _ ?sbs) ?sbt)) ?v ?A =>
    ceapply EqTrans ; [
      ceapply EqTrans ; [
        ceapply EqSym ; [
          ceapply EqTyConv ; [ ceapply EqSubstComp | .. ]
        | ..
        ]
      | ceapply EqTyConv ; [
          ceapply CongTermSubst ; [
            ceapply SubstRefl
          | ceapply EqSubstShiftZero
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
    then ceapply EqSym ; [ prepushsubst1 false | .. ]
    else fail "Not a goal handled by pushsubst: eqterm" G u v A
  | |- ?G => fail "Not a goal handled by pushsubst" G
  end.

Ltac pushsubst1 := prepushsubst1 true.

(* A lemma to do ZeroShift shifted, it not very robust as we would need
   some ZeroShift3 if ever we add a constructor that has three variables. *)
Lemma ZeroShift2 `{config.Reflection} :
  forall {G D A B C u sbs},
    eqtype D C (Subst B (sbzero A u)) ->
    isterm D u A ->
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    istype D C ->
    isctx G ->
    isctx D ->
    eqsubst (sbcomp (sbshift B (sbzero A u))
                    (sbshift C sbs))
            (sbcomp (sbshift B (sbshift A sbs))
                    (sbshift (Subst B (sbshift A sbs))
                             (sbzero (Subst A sbs) (subst u sbs))))
            (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
            (ctxextend (ctxextend D A) B).
Proof.
  intros.
  assert (isctx (ctxextend D A)).
  { ceapply CtxExtend ; assumption. }
  assert (istype D (Subst B (sbzero A u))).
  assert (issubst (sbzero A u) D (ctxextend D A)).
  { ceapply SubstZero ; assumption. }
  { ceapply TySubst ; eassumption. }
  assert (istype G (Subst C sbs)).
  { ceapply TySubst ; eassumption. }
  assert (istype G (Subst (Subst B (sbzero A u)) sbs)).
  { ceapply TySubst ; eassumption. }
  assert (isctx (ctxextend D C)).
  { ceapply CtxExtend ; assumption. }
  assert (isctx (ctxextend G (Subst C sbs))).
  { ceapply CtxExtend ; assumption. }
  assert (isctx (ctxextend G (Subst (Subst B (sbzero A u)) sbs))).
  { ceapply CtxExtend ; assumption. }
  assert (
    issubst (sbshift C sbs) (ctxextend G (Subst C sbs)) (ctxextend D C)
  ).
  { ceapply SubstShift ; assumption. }
  assert (eqctx G G).
  { ceapply CtxRefl. assumption. }
  assert (eqtype D (Subst B (sbzero A u)) C).
  { ceapply EqTySym ; assumption. }
  assert (eqtype G (Subst (Subst B (sbzero A u)) sbs) (Subst C sbs)).
  { ceapply CongTySubst ; [
      (config eapply @SubstRefl with (D := D)) ; assumption
    | assumption ..
    ].
  }
  assert (
    eqctx (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
    (ctxextend G (Subst C sbs))
  ).
  { ceapply EqCtxExtend ; assumption. }
  assert (eqctx D D).
  { ceapply CtxRefl. assumption. }
  assert (eqctx (ctxextend D (Subst B (sbzero A u))) (ctxextend D C)).
  { ceapply EqCtxExtend ; assumption. }
  assert (isctx (ctxextend D (Subst B (sbzero A u)))).
  { ceapply CtxExtend ; assumption. }
  assert (
    issubst (sbshift (Subst B (sbzero A u)) sbs)
            (ctxextend G (Subst C sbs))
            (ctxextend D C)
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (isctx (ctxextend (ctxextend D A) B)).
  { ceapply CtxExtend ; assumption. }
  assert (issubst (sbzero A u) D (ctxextend D A)).
  { ceapply SubstZero ; assumption. }
  assert (eqctx (ctxextend (ctxextend D A) B) (ctxextend (ctxextend D A) B)).
  { capply CtxRefl. assumption. }
  assert (
    issubst (sbshift B (sbzero A u)) (ctxextend D C)
            (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (eqtype G (Subst C sbs) (Subst (Subst B (sbzero A u)) sbs)).
  { ceapply EqTySym ; assumption. }
  assert (
    eqctx (ctxextend G (Subst C sbs))
          (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
  ).
  { ceapply EqCtxExtend ; assumption. }
  assert (eqctx (ctxextend D C) (ctxextend D C)).
  { capply CtxRefl. assumption. }
  assert (
    issubst (sbshift C sbs)
            (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
            (ctxextend D C)
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    eqctx (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
          (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
  ).
  { ceapply CtxRefl. assumption. }
  assert (
    issubst (sbshift (Subst B (sbzero A u)) sbs)
            (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
            (ctxextend D C)
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (issubst (sbcomp (sbzero A u) sbs) G (ctxextend D A)).
  { ceapply SubstComp ; eassumption. }
  assert (istype G (Subst B (sbcomp (sbzero A u) sbs))).
  { ceapply TySubst ; eassumption. }
  assert (
    eqtype G (Subst B (sbcomp (sbzero A u) sbs))
           (Subst (Subst B (sbzero A u)) sbs)
  ).
  { ceapply EqTySym ; [
      ceapply EqTySubstComp ; eassumption
    | assumption ..
    ].
  }
  assert (
    eqctx (ctxextend G (Subst B (sbcomp (sbzero A u) sbs)))
          (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
  ).
  { ceapply EqCtxExtend ; assumption. }
  assert (isctx (ctxextend G (Subst B (sbcomp (sbzero A u) sbs)))).
  { ceapply CtxExtend ; assumption. }
  assert (
    eqctx (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
          (ctxextend G (Subst B (sbcomp (sbzero A u) sbs)))
  ).
  { capply CtxSym ; assumption. }
  assert (
    eqctx (ctxextend D (Subst B (sbzero A u)))
          (ctxextend D (Subst B (sbzero A u)))
  ).
  { capply CtxRefl. assumption. }
  assert (
    issubst (sbshift (Subst B (sbzero A u)) sbs)
            (ctxextend G (Subst B (sbcomp (sbzero A u) sbs)))
            (ctxextend D (Subst B (sbzero A u)))
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    issubst (sbshift B (sbzero A u)) (ctxextend D (Subst B (sbzero A u)))
            (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstShift ; assumption. }
  assert (
    issubst
      (sbcomp (sbshift B (sbzero A u))
              (sbshift (Subst B (sbzero A u)) sbs))
      (ctxextend G (Subst B (sbcomp (sbzero A u) sbs)))
      (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstComp ; eassumption. }
  assert (
    eqctx (ctxextend G (Subst B (sbcomp (sbzero A u) sbs)))
          (ctxextend G (Subst B (sbcomp (sbzero A u) sbs)))
  ).
  { ceapply CtxRefl. assumption. }
  assert (
    issubst (sbshift B (sbcomp (sbzero A u) sbs))
            (ctxextend G (Subst B (sbcomp (sbzero A u) sbs)))
            (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (isterm G (subst u sbs) (Subst A sbs)).
  { ceapply TermSubst ; eassumption. }
  assert (istype G (Subst A sbs)).
  { ceapply TySubst ; eassumption. }
  assert (
    issubst (sbzero (Subst A sbs) (subst u sbs))
            G
            (ctxextend G (Subst A sbs))
  ).
  { ceapply SubstZero ; assumption. }
  assert (
    issubst (sbshift A sbs) (ctxextend G (Subst A sbs)) (ctxextend D A)
  ).
  { ceapply SubstShift ; assumption. }
  assert (isctx (ctxextend G (Subst A sbs))).
  { ceapply CtxExtend ; assumption. }
  assert (
    issubst (sbcomp (sbshift A sbs)
                    (sbzero (Subst A sbs) (subst u sbs))) G
            (ctxextend D A)
  ).
  { ceapply SubstComp ; eassumption. }
  assert (
    istype G
           (Subst B (sbcomp (sbshift A sbs)
                            (sbzero (Subst A sbs) (subst u sbs))))
  ).
  { ceapply TySubst ; eassumption. }
  assert (
    eqsubst (sbcomp (sbshift A sbs) (sbzero (Subst A sbs) (subst u sbs)))
            (sbcomp (sbzero A u) sbs)
            G
            (ctxextend D A)
  ).
  { ceapply ShiftZero ; assumption. }
  assert (eqtype (ctxextend D A) B B).
  { ceapply EqTyRefl ; assumption. }
  assert (
    eqtype G
           (Subst B (sbcomp (sbshift A sbs)
                            (sbzero (Subst A sbs) (subst u sbs))))
           (Subst B (sbcomp (sbzero A u) sbs))
  ).
  { ceapply CongTySubst ; eassumption. }
  assert (
    eqctx
      (ctxextend G
                 (Subst B
                        (sbcomp (sbshift A sbs)
                                (sbzero (Subst A sbs) (subst u sbs)))))
      (ctxextend G (Subst B (sbcomp (sbzero A u) sbs)))
  ).
  { ceapply EqCtxExtend ; assumption. }
  assert (
    isctx
      (ctxextend G
                 (Subst B (sbcomp (sbshift A sbs)
                                  (sbzero (Subst A sbs) (subst u sbs)))))
  ).
  { ceapply CtxExtend ; assumption. }
  assert (
    issubst
      (sbshift B
               (sbcomp (sbshift A sbs)
                       (sbzero (Subst A sbs) (subst u sbs))))
      (ctxextend G (Subst B (sbcomp (sbzero A u) sbs)))
      (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    eqtype G (Subst B (sbcomp (sbzero A u) sbs))
    (Subst B (sbcomp (sbshift A sbs) (sbzero (Subst A sbs) (subst u sbs))))
  ).
  { ceapply EqTySym ; assumption. }
  assert (
    eqtype G
    (Subst B (sbcomp (sbshift A sbs) (sbzero (Subst A sbs) (subst u sbs))))
    (Subst (Subst B (sbzero A u)) sbs)
  ).
  { ceapply EqTySym ; [
      ceapply EqTyTrans ; [
        ceapply EqTySubstComp ; eassumption
      | assumption ..
      ]
    | assumption ..
    ].
  }
  assert (
    eqctx
      (ctxextend G
                 (Subst B (sbcomp (sbshift A sbs)
                                  (sbzero (Subst A sbs) (subst u sbs)))))
      (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
  ).
  { ceapply EqCtxExtend ; assumption. }
  assert (istype (ctxextend G (Subst A sbs)) (Subst B (sbshift A sbs))).
  { ceapply TySubst ; eassumption. }
  assert (
    istype G
    (Subst (Subst B (sbshift A sbs)) (sbzero (Subst A sbs) (subst u sbs)))
  ).
  { ceapply TySubst ; eassumption. }
  assert (
    eqtype G
    (Subst (Subst B (sbshift A sbs)) (sbzero (Subst A sbs) (subst u sbs)))
    (Subst B (sbcomp (sbshift A sbs) (sbzero (Subst A sbs) (subst u sbs))))
  ).
  { ceapply EqTySubstComp ; eassumption. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Subst B (sbshift A sbs)) (sbzero (Subst A sbs) (subst u sbs))))
    (ctxextend G
       (Subst B (sbcomp (sbshift A sbs) (sbzero (Subst A sbs) (subst u sbs)))))
  ).
  { ceapply EqCtxExtend ; assumption. }
  assert (
    isctx (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift A sbs)))
  ).
  { ceapply CtxExtend ; assumption. }
  assert (
    eqctx (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift A sbs)))
    (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift A sbs)))
  ).
  { ceapply CtxRefl ; assumption. }
  assert (
    isctx
    (ctxextend G
       (Subst (Subst B (sbshift A sbs)) (sbzero (Subst A sbs) (subst u sbs))))
  ).
  { ceapply CtxExtend ; assumption. }
  assert (
    issubst
    (sbshift (Subst B (sbshift A sbs)) (sbzero (Subst A sbs) (subst u sbs)))
    (ctxextend G
       (Subst B (sbcomp (sbshift A sbs) (sbzero (Subst A sbs) (subst u sbs)))))
    (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift A sbs)))
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    issubst (sbshift B (sbshift A sbs))
    (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift A sbs)))
    (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstShift ; assumption. }
  assert (
    issubst
    (sbcomp (sbshift B (sbshift A sbs))
       (sbshift (Subst B (sbshift A sbs))
          (sbzero (Subst A sbs) (subst u sbs))))
    (ctxextend G
       (Subst B (sbcomp (sbshift A sbs) (sbzero (Subst A sbs) (subst u sbs)))))
    (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstComp ; eassumption. }
  assert (
    issubst
    (sbshift B (sbcomp (sbshift A sbs) (sbzero (Subst A sbs) (subst u sbs))))
    (ctxextend G
       (Subst B (sbcomp (sbshift A sbs) (sbzero (Subst A sbs) (subst u sbs)))))
    (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstShift ; assumption. }
  assert (
    eqtype G
    (Subst (Subst B (sbshift A sbs)) (sbzero (Subst A sbs) (subst u sbs)))
    (Subst (Subst B (sbzero A u)) sbs)
  ).
  { ceapply EqTyTrans ; [
      ceapply EqTySubstComp ; eassumption
    | ceapply EqTySym ; [
        ceapply EqTyTrans ; [
          ceapply EqTySubstComp ; eassumption
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
       (Subst (Subst B (sbshift A sbs)) (sbzero (Subst A sbs) (subst u sbs))))
    (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
  ).
  { ceapply EqCtxExtend ; assumption. }
  assert (
    issubst
    (sbshift (Subst B (sbshift A sbs)) (sbzero (Subst A sbs) (subst u sbs)))
    (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
    (ctxextend (ctxextend G (Subst A sbs)) (Subst B (sbshift A sbs)))
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    issubst
    (sbcomp (sbshift B (sbshift A sbs))
       (sbshift (Subst B (sbshift A sbs))
          (sbzero (Subst A sbs) (subst u sbs))))
    (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
    (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstComp ; eassumption. }
  assert (
    issubst
    (sbshift B (sbcomp (sbshift A sbs) (sbzero (Subst A sbs) (subst u sbs))))
    (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
    (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    issubst (sbshift B (sbcomp (sbzero A u) sbs))
    (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
    (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstCtxConv ; [
      ceapply SubstShift ; eassumption
    | assumption ..
    ].
  }
  assert (
    issubst
    (sbcomp (sbshift B (sbzero A u)) (sbshift (Subst B (sbzero A u)) sbs))
    (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
    (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstComp ; eassumption. }
  assert (
    issubst (sbcomp (sbshift B (sbzero A u)) (sbshift C sbs))
    (ctxextend G (Subst (Subst B (sbzero A u)) sbs))
    (ctxextend (ctxextend D A) B)
  ).
  { ceapply SubstComp ; eassumption. }




  ceapply SubstTrans ; [
    ceapply CongSubstComp ; [
      ceapply EqSubstCtxConv ; [
        ceapply CongSubstShift ; [
          (config eapply @SubstRefl with (D := D)) ; try assumption
        | eassumption
        | try assumption ..
        ]
      | ceapply EqCtxExtend ; try assumption
      | ceapply CtxRefl ; assumption
      | eassumption ..
      ]
    | ceapply SubstRefl ; assumption
    | assumption ..
    ]
  | ceapply SubstTrans ; [
      ceapply EqSubstCtxConv ; [
        config (eapply @CompShift with (E := ctxextend D A)) ; try assumption
      | eassumption ..
      ]
    | ceapply SubstTrans ; [
        ceapply EqSubstCtxConv ; [
          ceapply CongSubstShift ; [
             ceapply SubstSym ; [
               ceapply ShiftZero ; try assumption
             | eassumption ..
             ]
           | ceapply EqTyRefl ; eassumption
           | eassumption ..
           ]
        | eassumption ..
        ]
      | ceapply SubstTrans ; [
          ceapply SubstSym ; [
             ceapply EqSubstCtxConv ; [
                (config eapply @CompShift
                 with (D := ctxextend G (Subst A sbs))
                        (E := ctxextend D A)) ; try assumption
              | eassumption ..
              ]
           | assumption ..
           ]
        | ceapply SubstRefl ; assumption
        | assumption ..
        ]
      | assumption ..
      ]
    | assumption ..
    ]
  | assumption ..
  ].
  all:try assumption.
  2:eassumption.
  all:assumption.
Defined.

(* A simplify tactic to simplify substitutions *)
Ltac ecomp lm :=
  doConfig ;
  ceapply SubstTrans ; [
    ceapply CompAssoc
  | ceapply CongSubstComp ; [
      ceapply SubstRefl
    | ceapply lm
    | ..
    ]
  | ..
  ].

Ltac simplify_subst :=
  doConfig ;
  lazymatch goal with
  | |- eqsubst ?sbs ?sbt ?G ?D =>

      lazymatch sbs with

      | sbcomp (sbcomp ?sbs ?sbt) ?sbr =>
        ceapply SubstSym ; [
          ceapply CompAssoc
        | ..
        ]

      | sbcomp sbid ?sbs =>
        ceapply CompIdLeft

      | sbcomp ?sbs sbid =>
        ceapply CompIdRight

      | sbcomp (sbweak _) (sbzero _ _) =>
        ceapply WeakZero
      | sbcomp (sbweak _) (sbcomp (sbzero _ _) _) =>
        ecomp WeakZero

      | sbcomp (sbweak _) (sbshift _ _) =>
        ceapply WeakNat
      | sbcomp (sbweak _) (sbcomp (sbshift _ _) _) =>
        ecomp WeakNat

      | sbcomp (sbzero _ _) ?sbs =>
        ceapply SubstSym ; [ ceapply ShiftZero | .. ]

      | sbshift _ (sbcomp ?sbs ?sbt) =>
        ceapply SubstSym ; [ ceapply CompShift | .. ]
      | sbcomp (sbshift _ (sbcomp _ _)) _ =>
        ceapply SubstTrans ; [
          ceapply CompAssoc
        | ceapply CongSubstComp ; [
            ceapply SubstRefl
          | ceapply SubstSym ; [ ceapply CompShift | .. ]
          | ..
          ]
        | ..
        ]

      (* After ZeroShift, comes ZeroShift2 *)
      | sbcomp (sbshift _ (sbzero _ _)) (sbshift _ _) =>
        ceapply ZeroShift2
      | sbcomp (sbshift _ (sbzero _ _)) (sbcomp (sbshift _ _) _) =>
        ecomp ZeroShift2

      | sbcomp ?sbs ?sbt =>
        ceapply CongSubstComp ; [
          simplify_subst
        | ceapply SubstRefl
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
  doConfig ;
  lazymatch goal with
  | |- eqtype ?G (Subst ?A sbid) ?B =>
    ceapply EqTyTrans ; [
      ceapply EqTyIdSubst
    | ..
    ]

  | |- eqtype ?G (Subst ?A ?sbs) ?B =>
    ceapply EqTyTrans ; [
      ceapply CongTySubst ; [
        simplify_subst
      | ceapply EqTyRefl
      | ..
      ]
    | ..
    ]

  | |- eqterm ?G (subst ?u sbid) ?v ?A =>
    ceapply EqTrans ; [
      ceapply EqIdSubst
    | ..
    ]

  | |- eqterm ?G (subst ?u ?sbs) ?v ?A =>
    first [
      ceapply EqTrans ; [
        ceapply CongTermSubst ; [
          simplify_subst
        | ceapply EqRefl
        | ..
        ]
      | ..
      ]
    | ceapply EqTrans ; [
        ceapply EqTyConv ; [
          ceapply CongTermSubst ; [
            simplify_subst
          | ceapply EqRefl
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
  doConfig ;
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
  doConfig ;
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
            ceapply CongTySubst
          | myfail debug
          ] ; k try shelf true debug
          else first [
            ceapply EqTySym ; [ simplify | .. ]
          | ceapply CongTySubst
          | myfail debug
          ] ; k try shelf true debug
        )
        else first [
          pushsubst1
        | myfail debug
        ] ; k try shelf true debug
      | _ =>
        first [
          ceapply CongTySubst
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
          | ceapply CongTySubst
          | myfail debug
          ] ; k try shelf true debug
          else first [
            simplify
          | ceapply EqTySym ; [ simplify | .. ]
          | ceapply CongTySubst
          | myfail debug
          ] ; k try shelf true debug
        )
        else first [
          (* Should we simplify on the left first? *)
          pushsubst1
        | simplify
        | cando tysym ; ceapply EqTySym ; [ simplify | .. ]
        | myfail debug
        ] ; k try shelf true debug
      | _ =>
        first [
          simplify
        | ceapply CongTySubst
        | myfail debug
        ] ; k try shelf true debug
      end
  )
  else first [
    pushsubst1
  | cando tysym ; ceapply EqTySym ; [ simplify | .. ]
  | myfail debug
  ] ; k try shelf true debug.

(* Magic Tactic *)
(* It is basically a type checker that doesn't do the smart things,
   namely type and context conversions (and it doesn't rely on reflection
   obviously). *)
Ltac magicn try shelf tysym debug :=
  doConfig ;
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
      capply CtxEmpty
    | |- isctx (ctxextend ?G ?A) =>
      ceapply CtxExtend ; magicn try shelf true debug
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
    | |- issubst (sbzero _ ?u) ?G1 ?G2 =>
      first [
        ceapply SubstZero
      | ceapply SubstCtxConv ; [ ceapply SubstZero | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- issubst (sbweak _) ?G1 ?G2 =>
      first [
        ceapply SubstWeak
      | ceapply SubstCtxConv ; [ ceapply SubstWeak | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- issubst (sbshift _ ?sbs) ?G1 ?G2 =>
      first [
        ceapply SubstShift
      | ceapply SubstCtxConv ; [ ceapply SubstShift | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- issubst sbid ?G1 ?G2 =>
      first [
        ceapply SubstId
      | myfail debug
      ] ; magicn try shelf true debug
    | |- issubst (sbcomp ?sbt ?sbs) ?G1 ?G2 =>
      first [
        ceapply SubstComp
      | myfail debug
      ] ; magicn try shelf true debug
    | |- issubst ?sbs ?G1 ?G2 =>
      tryif (is_var sbs) then (
        first [
          eassumption
        | ceapply SubstCtxConv
        | myfail debug
        ] ; magicn try shelf tysym debug
      )
      else tryif (cando shelf)
        then shelve
        else myfail debug

    (*! Types !*)
    | |- istype ?G (Subst ?A ?sbs) =>
      first [
        ceapply TySubst
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G (Prod ?A ?B) =>
      first [
        ceapply TyProd
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G (Id ?A ?u ?v) =>
      first [
        ceapply TyId
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G Empty =>
      first [
        ceapply TyEmpty
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G Unit =>
      first [
        ceapply TyUnit
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G Bool =>
      first [
        ceapply TyBool
      | myfail debug
      ] ; magicn try shelf true debug
    | |- istype ?G ?A =>
      tryif (is_var A)
      then first [
        eassumption
      | ceapply TyCtxConv ; [ eassumption | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
      else tryif (cando shelf)
        then shelve
        else myfail debug

    (*! Terms !*)
    | |- isterm ?G (subst ?u ?sbs) ?A =>
      first [
        ceapply TermSubst
      | ceapply TermTyConv ; [
          ceapply TermSubst
        | ..
        ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm (ctxextend ?G ?A) (var 0) ?T =>
      first [
        ceapply TermVarZero
      | ceapply TermTyConv ; [ ceapply TermVarZero | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm (ctxextend ?G ?B) (var (S ?k)) ?A =>
      first [
        ceapply TermVarSucc
      | ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]
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
        ceapply TermAbs
      | ceapply TermTyConv ; [ ceapply TermAbs | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (app ?u ?A ?B ?v) ?C =>
      first [
        ceapply TermApp
      | ceapply TermTyConv ; [ ceapply TermApp | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (refl ?A ?u) ?B =>
      first [
        ceapply TermRefl
      | ceapply TermTyConv ; [ ceapply TermRefl | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (j ?A ?u ?C ?w ?v ?p) ?T =>
      first [
        ceapply TermJ
      | ceapply TermTyConv ; [ ceapply TermJ | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (exfalso ?A ?u) _ =>
      first [
        ceapply TermExfalso
      | ceapply TermTyConv ; [ ceapply TermExfalso | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G unit ?A =>
      first [
        ceapply TermUnit
      | ceapply TermTyConv ; [ ceapply TermUnit | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G true ?A =>
      first [
        ceapply TermTrue
      | ceapply TermTyConv ; [ ceapply TermTrue | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G false ?A =>
      first [
        ceapply TermFalse
      | ceapply TermTyConv ; [ ceapply TermFalse | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- isterm ?G (cond ?C ?u ?v ?w) ?T =>
      first [
        ceapply TermCond
      | ceapply TermTyConv ; [ ceapply TermCond | .. ]
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
        | ceapply TermTyConv ; [ eassumption | .. ]
        | ceapply TermCtxConv ; [ eassumption | .. ]
        | ceapply TermCtxConv ; [
            ceapply TermTyConv ; [ eassumption | .. ]
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
      capply EqCtxEmpty
    | |- eqctx (ctxextend ?G ?A) (ctxextend ?D ?B) =>
      first [
        ceapply EqCtxExtend
      | capply CtxSym ; [ ceapply EqCtxExtend | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqctx ?G ?G =>
      first [
        ceapply CtxRefl
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqctx ?G ?D =>
      tryif (is_var G ; is_var D)
      then first [
        assumption
      | capply CtxSym ; [ assumption | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
      else tryif (cando shelf)
        then shelve
        else myfail debug

    (*! Equality of substitutions !*)
    | |- eqsubst (sbcomp (sbweak _) (sbshift _ ?sbs))
                (sbcomp ?sbs (sbweak _)) ?G ?D =>
      first [
        ceapply WeakNat
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqsubst (sbcomp ?sbs (sbweak _))
                (sbcomp (sbweak _) (sbshift _ ?sbs)) ?G ?D =>
      first [
        ceapply SubstSym ; [ ceapply WeakNat | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqsubst (sbzero _ ?u1) (sbzero _ ?u2) ?D ?E =>
      first [
        ceapply CongSubstZero
      | ceapply EqSubstCtxConv ; [ ceapply CongSubstZero | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqsubst (sbweak _) (sbweak _) ?D ?E =>
      first [
        ceapply CongSubstWeak
      | ceapply EqSubstCtxConv ; [ ceapply CongSubstWeak | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqsubst (sbshift _ ?sbs1) (sbshift _ ?sbs2) ?D ?E =>
      first [
        ceapply CongSubstShift
      | ceapply EqSubstCtxConv ; [ ceapply CongSubstShift | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqsubst ?sbs ?sbs ?G ?D =>
      first [
          ceapply SubstRefl
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
      | ceapply SubstSym ; [ eassumption | .. ]
      | ceapply EqSubstCtxConv ; [ eassumption | .. ]
      | ceapply SubstSym ; [
          ceapply EqSubstCtxConv ; [ eassumption | .. ]
        | ..
        ]
      | myfail debug
      ] ; magicn try shelf true debug
      else first [
        ceapply SubstTrans ; [ simplify_subst | .. ]
      | ceapply SubstSym ; [ ceapply SubstTrans ; [ simplify_subst | .. ] | .. ]
      | ceapply CongSubstComp
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
    | |- eqtype ?G (Subst ?A (sbshift ?A2 ?sbs))
               (Subst ?B' (sbcomp ?sbs (sbweak (Subst ?A1 ?sbs)))) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := (Subst B' (sbweak _)))
        | myfail debug
        ] ; magicn try shelf true debug
      )
      else eqtype_subst G A (sbshift A2 sbs)
                        (Subst B' (sbcomp sbs (sbweak (Subst A1 sbs))))
                        magicn try shelf tysym debug
    | |- eqtype ?G (Subst ?B' (sbcomp ?sbs (sbweak (Subst ?A1 ?sbs))))
               (Subst ?A (sbshift ?A2 ?sbs)) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := Subst B' (sbweak _))
        | myfail debug
        ] ; magicn try shelf true debug
      )
      else eqtype_subst G (Subst B' (sbcomp sbs (sbweak A1 sbs)))
                        (Subst A (sbshift A2 sbs))
                        magicn try shelf tysym debug
    | |- eqtype ?G
               (Subst ?A
                      (sbcomp (sbshift ?A1 ?sbs)
                              (sbzero ?A2 (subst ?u ?sbs))))
               (Subst ?B' ?sbs) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := Subst B' (sbweak _))
        | myfail debug
        ] ; magicn try shelf true debug
      )
      else eqtype_subst G
                        A
                        (sbcomp (sbshift A1 sbs)
                                (sbzero A2 (subst u sbs)))
                        (Subst B' sbs)
                        magicn try shelf tysym debug
    | |- eqtype ?G (Subst ?B' ?sbs)
               (Subst ?A (sbcomp (sbshift ?A1 ?sbs)
                                 (sbzero ?A2 (subst ?u ?sbs)))) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := Subst B' (sbweak _))
        | myfail debug
        ] ; magicn try shelf true debug
      )
      else eqtype_subst G B' sbs
                        (Subst A (sbcomp (sbshift A1 sbs)
                                         (sbzero A2 (subst u sbs))))
                        magicn try shelf tysym debug
    (* Another case I'm not sure of. *)
    | |- eqtype ?G
               (Subst ?A ?sbs)
               (Subst ?B (sbzero (Subst ?A ?sbs) (subst ?u ?sbs))) =>
      tryif (is_var A ; is_evar B)
      then
        first [
          instantiate (1 := Subst (Subst A sbs) (sbweak _))
        | myfail debug
        ] ; magicn try shelf true debug
      else
        eqtype_subst G A sbs (Subst B (sbzero (Subst A sbs) (subst u sbs)))
                     magicn try shelf tysym debug
    (* One more *)
    | |- eqtype ?G (Subst ?A (sbzero ?B' ?u)) ?B =>
      tryif (is_evar A ; is_var B)
      then first [
        instantiate (1 := Subst B (sbweak _))
      | myfail debug
      ] ; magicn try shelf true debug
      else eqtype_subst G A (sbzero B u) B
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
      then ceapply EqTySym ; [
        magicn try shelf false debug
      | magicn try shelf true debug ..
      ]
      else myfail debug
    | |- eqtype ?G (Id ?A ?u ?v) (Id ?B ?w ?z) =>
      first [
        ceapply CongId
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqtype ?G (Prod ?A ?B) (Prod ?C ?D) =>
      first [
        ceapply CongProd
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqtype ?G Unit Unit =>
      first [
        ceapply EqTyRefl
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqtype ?G Bool Bool =>
      first [
        ceapply EqTyRefl
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqtype ?G ?A ?B =>
      tryif (is_var A ; is_var B)
      then (
        first [
          eassumption
        | ceapply EqTyRefl
        | ceapply EqTySym ; [ eassumption | .. ]
        | ceapply EqTyCtxConv ; [
            first [
              eassumption
            | ceapply EqTySym ; [ eassumption | .. ]
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
                ceapply CongTermSubst
              | ceapply EqTyConv ; [
                  ceapply CongTermSubst
                | ..
                ]
              | eassumption
              | myfail debug
              ] ; magicn try shelf true debug
              else first [
                ceapply EqSym ; [ simplify | .. ]
              | ceapply CongTermSubst
              | ceapply EqTyConv ; [
                  ceapply CongTermSubst
                | ..
                ]
              | myfail debug
              ] ; magicn try shelf true debug
            )
            else first [
              pushsubst1
            | ceapply EqSym ; [ pushsubst1 | .. ]
            | cando shelf ; shelve
            ] ; magicn try shelf true debug
          | _ =>
            first [
              ceapply CongTermSubst
            | ceapply EqTyConv ; [
              ceapply CongTermSubst
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
              | ceapply CongTermSubst
              | ceapply EqTyConv ; [ ceapply CongTermSubst | .. ]
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
      then ceapply EqSym ; [
        magicn try shelf false debug
      | magicn try shelf true debug ..
      ]
      else myfail debug
    | |- eqterm ?G ?u ?u ?A =>
      first [
        ceapply EqRefl
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G ?u ?v Empty =>
      first [
        config eapply @EqTermExfalso with (w := u)
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G ?u ?v Unit =>
      first [
        ceapply UnitEta
      | myfail debug
      ] ; magicn try shelf true debug
    (* Where should ProdBeta be handled? *)
    (* Same for CondTrue, CondFalse, JRefl *)
    (* ProdEta should come in after CongApp and CongProd probably *)
    | |- eqterm ?G (lam ?A1 ?A2 ?u1) (lam ?B1 ?B2 ?u2) _ =>
      first [
        ceapply CongAbs
      | ceapply EqTyConv ; [ ceapply CongAbs | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G (app ?u1 ?A1 ?A2 ?u2) (app ?v1 ?B1 ?B2 ?v2) _ =>
      first [
        ceapply CongApp
      | ceapply EqTyConv ; [ ceapply CongApp | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G (refl ?A1 ?u1) (refl ?A2 ?u2) _ =>
      first [
        ceapply CongRefl
      | ceapply EqTyConv ; [ ceapply CongRefl | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G (j ?A1 ?u1 ?C1 ?w1 ?v1 ?p1) (j ?A2 ?u2 ?C2 ?w2 ?v2 ?p2) _ =>
      first [
        ceapply CongJ
      | ceapply EqTyConv ; [ ceapply CongJ | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G (cond ?C1 ?u1 ?v1 ?w1) (cond ?C2 ?u2 ?v2 ?w2) _ =>
      first [
        ceapply CongCond
      | ceapply EqTyConv ; [ ceapply CongCond | .. ]
      | myfail debug
      ] ; magicn try shelf true debug
    | |- eqterm ?G ?u ?v ?A =>
      tryif (is_var u ; is_var v)
      then first [
        eassumption
      | ceapply EqRefl
      | ceapply EqSym ; [ eassumption |.. ]
      | ceapply EqTyConv ; [ eassumption | .. ]
      | ceapply EqTyConv ; [
          ceapply EqSym ; [ eassumption | .. ]
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
  doConfig ;
  match goal with
  | |- eqterm _ _ _ _ => idtac
  | |- eqtype _ _ _ => idtac
  | |- eqsubst _ _ _ _ => idtac
  | |- eqctx _ _ => idtac
  | _ => shelve
  end.