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
    istype G (Subst (Subst A sbt) sbs) ->
    istype G (Subst A (sbcomp sbt sbs)) ->
    eqtype G (Subst (Subst A sbt) sbs) B.
Proof.
  intros.
  eapply EqTyTrans ; [
    eapply EqTySubstComp ; eassumption
  | assumption ..
  ].
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
    istype G (Subst (Subst A sbt) sbs) ->
    istype G (Subst A (sbcomp sbt sbs)) ->
    isterm G (subst (subst u sbt) sbs) (Subst A (sbcomp sbt sbs)) ->
    isterm G (subst u (sbcomp sbt sbs)) (Subst A (sbcomp sbt sbs)) ->
    isterm G v (Subst A (sbcomp sbt sbs)) ->
    eqterm G (subst (subst u sbt) sbs) v (Subst (Subst A sbt) sbs).
Proof.
  intros.
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
    eapply EqTySym ; try eapply eqtype_subst_left
  | |- eqterm ?G (subst (subst ?u ?sbt) ?sbs) ?v (Subst (Subst ?A ?sbt) ?sbs) =>
    eapply eqterm_subst_left
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) (Subst (Subst ?A ?sbt) ?sbs) =>
    eapply EqSym ; try eapply eqterm_subst_left
  | |- eqterm ?G (subst (subst ?u ?sbt) ?sbs) ?v ?A =>
    eapply EqTyConv ; [ try eapply eqterm_subst_left | .. ]
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) ?A =>
    eapply EqSym ; [
      eapply EqTyConv ; [ try eapply eqterm_subst_left | .. ]
    | ..
    ]
  | _ => fail
  end.


Lemma EqCompZero :
  forall {G D A u sbs},
    issubst sbs G D ->
    isterm D u A ->
    istype D A ->
    isctx G ->
    isctx D ->
    eqterm G
           (subst (var 0) (sbcomp (sbzero u) sbs))
           (subst u sbs)
           (Subst A sbs).
Proof.
  intros.
  assert (istype G (Subst A sbs)).
  { eapply TySubst ; eassumption. }
  assert (isterm G (subst u sbs) (Subst A sbs)).
  { eapply TermSubst ; eassumption. }
  assert (issubst (sbzero u) D (ctxextend D A)).
  { eapply SubstZero ; eassumption. }
  assert (isctx (ctxextend D A)).
  { eapply CtxExtend ; assumption. }
  assert (issubst (sbcomp (sbzero u) sbs) G (ctxextend D A)).
  { eapply SubstComp ; eassumption. }
  assert (isterm (ctxextend D A) (var 0) (Subst A sbweak)).
  { apply TermVarZero ; assumption. }
  assert (issubst sbweak (ctxextend D A) D).
  { eapply SubstWeak ; assumption. }
  assert (istype (ctxextend D A) (Subst A sbweak)).
  { eapply TySubst ; eassumption. }
  assert (
    isterm G
           (subst (var 0) (sbcomp (sbzero u) sbs))
           (Subst (Subst A sbweak) (sbcomp (sbzero u) sbs))
  ).
  { eapply TermSubst ; eassumption. }
  assert (istype G (Subst (Subst A sbweak) (sbcomp (sbzero u) sbs))).
  { eapply TySubst ; eassumption. }
  assert (issubst (sbcomp sbweak (sbcomp (sbzero u) sbs)) G D).
  { eapply SubstComp ; eassumption. }
  assert (istype G (Subst A (sbcomp sbweak (sbcomp (sbzero u) sbs)))).
  { eapply TySubst ; eassumption. }
  assert (issubst (sbcomp sbweak (sbzero u)) D D).
  { eapply SubstComp ; eassumption. }
  assert (issubst sbid D D).
  { apply SubstId. assumption. }
  assert (issubst (sbcomp (sbcomp sbweak (sbzero u)) sbs) G D).
  { eapply SubstComp ; eassumption. }
  assert (issubst (sbcomp sbid sbs) G D).
  { eapply SubstComp ; eassumption. }
  assert (eqsubst (sbcomp sbweak (sbcomp (sbzero u) sbs)) sbs G D).
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
    eqtype G (Subst (Subst A sbweak) (sbcomp (sbzero u) sbs)) (Subst A sbs)
  ).
  { compsubst1 ; try eassumption.
    eapply CongTySubst ; eassumption.
  }
  assert (isterm G (subst (var 0) (sbcomp (sbzero u) sbs)) (Subst A sbs)).
  { eapply TermTyConv ; eassumption. }
  assert (istype D (Subst (Subst A sbweak) (sbzero u))).
  { eapply TySubst ; eassumption. }
  assert (istype D (Subst A sbid)).
  { eapply TySubst ; eassumption. }
  assert (eqtype D (Subst A sbid) A).
  { eapply EqTyIdSubst ; eassumption. }
  assert (eqtype D A (Subst A sbid)).
  { eapply EqTySym ; eassumption. }
  assert (isterm D u (Subst A sbid)).
  { eapply TermTyConv ; eassumption. }
  assert (istype D (Subst A (sbcomp sbweak (sbzero u)))).
  { eapply TySubst ; eassumption. }
  assert (eqtype D (Subst (Subst A sbweak) (sbzero u)) A).
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
  assert (isterm D (subst (var 0) (sbzero u)) A).
  { eapply TermTyConv ; [
      eapply TermSubst
    | ..
    ] ; eassumption.
  }
  assert (
    eqtype G (Subst A sbs) (Subst (Subst A sbweak) (sbcomp (sbzero u) sbs))
  ).
  { eapply EqTySym ; eassumption. }
  assert (
    isterm G
           (subst (subst (var 0) (sbzero u)) sbs)
           (Subst (Subst A sbweak) (sbcomp (sbzero u) sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst
    | ..
    ] ; eassumption.
  }
  assert (isterm G (subst (subst (var 0) (sbzero u)) sbs) (Subst A sbs)).
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



(* Some tactic to push substitutions inside one step. *)
(* Partial for now. *)
Ltac pushsubst1 :=
  lazymatch goal with
  (*! Pushing in types !*)
  (* Is this first goal ever necessary? *)
  | |- eqtype ?G (Subst (Subst ?A ?sbs) ?sbt) ?B =>
    eapply EqTyTrans ; [
      eapply CongTySubst ; [
        eapply SubstRefl
      | pushsubst1
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
  (* Now, we deal with a very particuliar case. *)
  | |- eqtype ?G (Subst ?A (sbzero ?u)) ?B' =>
    (* tryif (is_evar A ; is_var B') *)
    tryif (is_evar A)
    then (
      eapply @EqTyTrans with (B := Subst (Subst B' sbweak) (sbzero u)) ; [
        eapply EqTyRefl
      | ..
      ]
    )
    else fail
  (*! Pushing in terms !*)
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    eapply EqTrans ; [ eapply EqSubstRefl | .. ]
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    eapply EqTyConv ; [
      eapply EqTrans ; [ eapply EqSubstRefl | .. ]
    | ..
    ]
  | |- eqterm ?G (subst true ?sbs) ?u ?A =>
    eapply EqTrans ; [ eapply EqSubstTrue | .. ]
  | |- eqterm ?G (subst true ?sbs) ?u ?A =>
    eapply EqTyConv ; [
      eapply EqTrans ; [ eapply EqSubstTrue | .. ]
    | ..
    ]
  | |- eqterm ?G (subst false ?sbs) ?u ?A =>
    eapply EqTrans ; [ eapply EqSubstFalse | .. ]
  | |- eqterm ?G (subst false ?sbs) ?u ?A =>
    eapply EqTyConv ; [
      eapply EqTrans ; [ eapply EqSubstFalse | .. ]
    | ..
    ]
  | |- eqterm ?G (subst (var 0) (sbzero ?u)) ?v ?A =>
    eapply EqTrans ; [ eapply EqSubstZeroZero | .. ]
  | |- eqterm ?G ?u (subst (var 0) (sbzero ?v)) ?A =>
    eapply EqSym ; [ eapply EqTrans ; [ eapply EqSubstZeroZero | .. ] | .. ]
  | |- eqterm ?G (subst (var 0) (sbshift ?sbs)) ?v ?A =>
    eapply EqTrans ; [
      eapply EqTyConv ; [
        eapply EqSubstShiftZero
      | ..
      ]
    | ..
    ]
  | |- eqterm ?G ?u (subst (var 0) (sbshift ?sbs)) ?A =>
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
  | |- eqterm ?G (subst (var 0) (sbcomp (sbzero ?u) ?sbt)) ?v ?A =>
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
  | |- eqterm ?G (subst (var 0) (sbcomp (sbshift ?sbs) ?sbt)) ?v ?A =>
    eapply EqTrans ; [
      eapply EqTrans ; [
        eapply EqSym ; [
          eapply EqTyConv ; [ eapply EqSubstComp | .. ]
        | ..
        ]
      | eapply EqTyConv ; [
          eapply CongTermSubst ; [
            idtac
          | eapply EqSubstShiftZero
          | ..
          ]
        | ..
        ]
      | ..
      ]
    | ..
    ]
  (* Similarly, peculiar cases. *)
  (* | |- eqterm ?G (subst ?w (sbzero ?u)) ?u ?A => *)
    (* Since it would imply a choice that I don't know how to enforce,
       I have to remove this case. *)
    (* tryif (is_evar w ; is_var u) *)
    (* then first [ *)
    (*   eapply @EqTrans with (v := subst (var 0) (sbzero u)) ; [ *)
    (*     eapply EqRefl *)
    (*   | .. *)
    (*   ] *)
    (* | eapply @EqTrans with (v := subst (subst u sbweak) (sbzero u))  ; [ *)
    (*     eapply EqRefl *)
    (*   | .. *)
    (*   ] *)
    (* ] *)
    (* else *) (* fail *)
  (* | |- eqterm ?G (subst ?w (sbzero ?v')) ?u ?A => *)
  (*   tryif (is_evar w ; is_var u) *)
  (*   then ( *)
  (*     eapply @EqTrans with (v := subst (subst u sbweak) (sbzero v'))  ; [ *)
  (*       eapply EqRefl *)
  (*     | .. *)
  (*     ] *)
  (*   ) *)
  (*   else fail *)
  | _ => fail
  end.

Ltac cando token :=
  match token with
  | true => idtac
  | false => fail
  end.

(* Simplify tactic *)
(* Its purpose is simplifying substitutions in equalities,
   assuming the substitution is on the left. *)
Ltac simplify :=
  lazymatch goal with
  | |- eqtype ?G (Subst ?A ?sbs) ?B =>
    tryif (is_var sbs)
    then fail
    else
      lazymatch sbs with
      (* This case is unsatisfying... We would like to linearize substitutions
         when they are composed. *)
      | sbcomp (sbcomp sbweak (sbcomp (sbzero ?u) ?sbs)) ?sbt =>
        eapply EqTyTrans ; [
          eapply CongTySubst ; [
            eapply CongSubstComp ; [
              eapply SubstRefl
            | eapply SubstTrans ; [
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
              ]
            | ..
            ]
          | ..
          ]
        | ..
        ]
      | sbcomp ?sbt (sbcomp (sbshift ?sbs) (sbzero (subst ?u ?sbs))) =>
        eapply EqTyTrans ; [
          eapply CongTySubst ; [
            eapply CongSubstComp ; [
              eapply ShiftZero
            | eapply SubstRefl
            | ..
            ]
          | ..
          ]
        | ..
        ]
      | sbcomp (sbcomp ?sbt (sbshift ?sbs)) (sbzero (subst ?u ?sbs)) =>
        eapply EqTyTrans ; [
          eapply CongTySubst ; [
            eapply SubstTrans ; [
              eapply SubstSym ; [ eapply CompAssoc | .. ]
            | eapply CongSubstComp ; [
                eapply ShiftZero
              | eapply SubstRefl
              | ..
              ]
            | ..
            ]
          | ..
          ]
        | ..
        ]
      | sbcomp sbweak (sbcomp (sbzero ?u) ?sbt) =>
        eapply EqTyTrans ; [
          eapply CongTySubst ; [
            eapply SubstTrans ; [
              eapply CompAssoc
            | eapply CongSubstComp ; [
                idtac
              | eapply WeakZero
              | ..
              ]
            | ..
            ]
          | ..
          ]
        | ..
        ]
      | sbcomp (sbcomp sbweak (sbzero ?u)) ?sbt =>
        eapply EqTyTrans ; [
          eapply CongTySubst ; [
            eapply CongSubstComp ; [
              idtac
            | eapply WeakZero
            | ..
            ]
          | ..
          ]
        | ..
        ]
      | sbcomp ?sbs (sbcomp sbweak (sbzero ?u)) =>
        eapply EqTyTrans ; [
          eapply CongTySubst ; [
            eapply CongSubstComp ; [
              eapply WeakZero
            | ..
            ]
          | ..
          ]
        | ..
        ]
      | sbcomp sbid ?sbs =>
        eapply EqTyTrans ; [
          eapply CongTySubst ; [
            eapply CompIdLeft
          | ..
          ]
        | ..
        ]
      | sbcomp ?sbs sbid =>
        eapply EqTyTrans ; [
          eapply CongTySubst ; [
            eapply CompIdRight
          | ..
          ]
        | ..
        ]
      | sbcomp sbweak (sbzero ?u) =>
        eapply EqTyTrans ; [
          eapply CongTySubst ; [
            eapply WeakZero
          | ..
          ]
        | ..
        ]
      | sbid =>
        eapply EqTyTrans ; [
          eapply EqTyIdSubst
        | ..
        ]
      end
  | |- eqterm ?G (subst ?u ?sbs) ?v ?A =>
    tryif (is_var sbs)
    then fail
    else
      lazymatch sbs with
      | sbcomp ?sbt (sbcomp (sbshift ?sbs) (sbzero (subst ?u ?sbs))) =>
        eapply EqTrans ; [
          eapply CongTermSubst ; [
            eapply CongSubstComp ; [
              eapply ShiftZero
            | eapply SubstRefl
            | ..
            ]
          | ..
          ]
        | ..
        ]
      | sbcomp (sbcomp ?sbt (sbshift ?sbs)) (sbzero (subst ?u ?sbs)) =>
        eapply EqTrans ; [
          eapply CongTermSubst ; [
            eapply SubstTrans ; [
              eapply SubstSym ; [ eapply CompAssoc | .. ]
            | eapply CongSubstComp ; [
                eapply ShiftZero
              | eapply SubstRefl
              | ..
              ]
            | ..
            ]
          | ..
          ]
        | ..
        ]
      | sbcomp sbweak (sbcomp (sbzero ?u) ?sbt) =>
        first [
          eapply EqTrans ; [
            eapply CongTermSubst ; [
              eapply SubstTrans ; [
                eapply CompAssoc
              | eapply CongSubstComp ; [
                  idtac
                | eapply WeakZero
                | ..
                ]
              | ..
              ]
            | ..
            ]
          | ..
          ]
        | eapply EqTrans ; [
            eapply EqTyConv ; [
              eapply CongTermSubst ; [
                eapply SubstTrans ; [
                  eapply CompAssoc
                | eapply CongSubstComp ; [
                    idtac
                  | eapply WeakZero
                  | ..
                  ]
                | ..
                ]
              | ..
              ]
            | ..
            ]
          | ..
          ]
        ]
      | sbcomp sbid ?sbs =>
        first [
          eapply EqTrans ; [
            eapply CongTermSubst ; [
              eapply CompIdLeft
            | ..
            ]
          | ..
          ]
        | eapply EqTrans ; [
            eapply EqTyConv ; [
              eapply CongTermSubst ; [
                eapply CompIdLeft
              | ..
              ]
            | ..
            ]
          | ..
          ]
        ]
      | sbcomp sbweak (sbzero ?u) =>
        eapply EqTrans ; [
          eapply CongTermSubst ; [
            eapply WeakZero
          | ..
          ]
        | ..
        ]
      | sbid =>
        eapply EqTrans ; [
          eapply EqIdSubst
        | ..
        ]
      end
  | _ => fail
  end.

(* Checking if we're dealing with a suitable goal. *)
(* This would be interesting in another file maybe? *)
Ltac check_goal :=
  match goal with
  | |- isctx ?G => idtac
  | |- issubst ?sbs ?G ?D => idtac
  | |- istype ?G ?A => idtac
  | |- isterm ?G ?u ?A => idtac
  | |- eqctx ?G ?D => idtac
  | |- eqsubst ?sbs ?sbt ?G ?D => idtac
  | |- eqtype ?G ?A ?B => idtac
  | |- eqterm ?G ?u ?v ?A => idtac
  | _ => fail
  end.

(* Factorizing some cases *)
Ltac eqtype_subst G A sbs B k n try shelf tysym :=
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
            eapply CongTySubst ; k n try shelf true
          | eassumption
          ]
          else first [
            eapply EqTySym ; [ simplify | .. ] ; k n try shelf true
          | eapply CongTySubst ; k n try shelf true
          ]
        )
        else pushsubst1 ; k n try shelf true
      | _ =>
        first [
          eapply CongTySubst ; k n try shelf true
        | eassumption
        ]
      end
    )
    else first [
      simplify ; k n try shelf true
    | eapply CongTySubst ; k n try shelf true
    ]
  )
  else first [
    pushsubst1
  | cando tysym ; eapply EqTySym ; [ simplify | .. ]
  ] ; k n try shelf true.

(* Magic Tactic *)
(* It is basically a type checker that doesn't do the smart things,
   namely type and context conversions (and it doesn't rely on reflection
   obviously). *)
Ltac magicn n try shelf tysym :=
  (* We only ever apply magic to suitable goals *)
  check_goal ;
  first [
    assumption
  | (* We have several things we need to do to the tactic:
       * Only use assumption on the base cases (not on SubstZero and the like).
       * Remove the _ case.
       * Add special rules when dealing with substitution typing this can go
         though special admissibility rules that factorize the number of
         premises that would be needed to prove.
       * Should it be able to use EqTyWeakNat?
       * Add a token to solve equalities with only one side as reflexivity.
         (Maybe shelve them in the meantime?)
       * Put tysym token back to true whenever progress is made
         (ie not when using structural rules).
       * ... *)
    lazymatch goal with
    (*! Contexts !*)
    | |- isctx ctxempty =>
      apply CtxEmpty
    | |- isctx (ctxextend ?G ?A) =>
      eapply CtxExtend ; magicn n try shelf true
    | |- isctx ?G =>
      (* And not eassumption so we don't select some random context. *)
      assumption || cando shelf ; shelve
    (*! Substitutions !*)
    | |- issubst (sbzero ?u) ?G1 ?G2 =>
      first [
          eapply SubstZero ; magicn n try shelf true
        | eassumption
        ]
    | |- issubst sbweak ?G1 ?G2 =>
      first [
          eapply SubstWeak ; magicn n try shelf true
        | assumption
        | cando shelf ; shelve
        ]
    | |- issubst (sbshift ?sbs) ?G1 ?G2 =>
      first [
          eapply SubstShift ; magicn n try shelf true
        | eassumption
        | eapply SubstCtxConv ; magicn n try shelf tysym
        ]
    | |- issubst (sbid) ?G1 ?G2 =>
      first [
          eapply SubstId ; magicn n try shelf true
        | eassumption
        ]
    | |- issubst (sbcomp ?sbt ?sbs) ?G1 ?G2 =>
      first [
          eapply SubstComp ; magicn n try shelf true
        | eassumption
        ]
    | |- issubst ?sbs ?G1 ?G2 =>
      tryif (is_var sbs) then (
        first [
          eassumption
        | eapply SubstCtxConv ; magicn n try shelf tysym
        ]
      ) else (cando shelf ; shelve)
    (*! Types !*)
    | |- istype ?G (Subst ?A ?sbs) =>
      eapply TySubst ; magicn n try shelf true
    | |- istype ?G (Prod ?A ?B) =>
      eapply TyProd ; magicn n try shelf true
    | |- istype ?G (Id ?A ?u ?v) =>
      eapply TyId ; magicn n try shelf true
    | |- istype ?G Empty =>
      eapply TyEmpty ; magicn n try shelf true
    | |- istype ?G Unit =>
      eapply TyUnit ; magicn n try shelf true
    | |- istype ?G Bool =>
      eapply TyBool ; magicn n try shelf true
    | |- istype ?G ?A =>
      tryif (is_var A)
      then first [
        eassumption
      | eapply TyCtxConv ; [
          eassumption
        | magicn n try shelf true ..
        ]
      ]
      else first [
        assumption
      | cando shelf ; shelve
      ]
    (*! Terms !*)
    | |- isterm ?G (subst ?u ?sbs) ?A =>
      first [
        eapply TermSubst ; magicn n try shelf true
      | eapply TermTyConv ; [
          eapply TermSubst ; magicn n try shelf true
        | magicn n try shelf true ..
        ]
      ]
    | |- isterm (ctxextend ?G ?A) (var 0) ?T =>
      first [
        eapply TermVarZero ; magicn n try shelf true
      | eapply TermTyConv ; [ eapply TermVarZero | .. ] ;
        magicn n try shelf true
      ]
    | |- isterm (ctxextend ?G ?B) (var (S ?k)) (Subst ?A sbweak) =>
      eapply TermVarSucc ; magicn n try shelf true
    | |- isterm ?G (lam ?A ?B ?u) ?C =>
      first [
        eapply TermAbs ; magicn n try shelf true
      | eapply TermTyConv ; [
          eapply TermAbs ; magicn n try shelf true
        | magicn n try shelf true ..
        ]
      ]
    | |- isterm ?G (app ?u ?A ?B ?v) ?C =>
      first [
        eapply TermApp ; magicn n try shelf true
      | eapply TermTyConv ; [ eapply TermApp | .. ] ; magicn n try shelf true
      ]
    | |- isterm ?G (refl ?A ?u) ?B =>
      first [
        eapply TermRefl ; magicn n try shelf true
      | eapply TermTyConv ; [ eapply TermRefl | .. ] ; magicn n try shelf true
      ]
    | |- isterm ?G (j ?A ?u ?C ?w ?v ?p) ?T =>
      first [
        eapply TermJ ; magicn n try shelf true
      | eapply TermTyConv ; [ eapply TermJ | .. ] ; magicn n try shelf true
      ]
    | |- isterm ?G (exfalso ?A ?u) _ =>
      eapply TermExfalso ; magicn n try shelf true
    | |- isterm ?G unit ?A =>
      first [
          eapply TermUnit ; magicn n try shelf true
        | eapply TermTyConv ; [
            eapply TermUnit ; magicn n try shelf true
          | magicn n try shelf true
          ]
        ]
    | |- isterm ?G true ?A =>
      first [
          eapply TermTrue ; magicn n try shelf true
        | eapply TermTyConv ; [
            eapply TermTrue ; magicn n try shelf true
          | magicn n try shelf true
          ]
        ]
    | |- isterm ?G false ?A =>
      first [
          eapply TermFalse ; magicn n try shelf true
        | eapply TermTyConv ; [
            eapply TermFalse ; magicn n try shelf true
          | magicn n try shelf true
          ]
        ]
    | |- isterm ?G (cond ?C ?u ?v ?w) ?T =>
      first [
        eapply TermCond ; magicn n try shelf true
      | eapply TermTyConv ; [ eapply TermCond | .. ] ;
        magicn n try shelf true
      ]
    (* This might go away some day. *)
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
      then (cando shelf ; shelve)
      else (
        tryif (is_var u)
        then first [
          eassumption
        | eapply TermTyConv ; [
            eassumption
          | magicn n try shelf true ..
          ]
        | eapply TermCtxConv ; [
            eassumption
          | magicn n try shelf true ..
          ]
        | eapply TermCtxConv ; [
            eapply TermTyConv ; [
              eassumption
            | magicn n try shelf true ..
            ]
          | magicn n try shelf true ..
          ]
        ]
        else cando shelf ; shelve
      )
    (*! Equality of contexts !*)
    | |- eqctx ctxempty ctxempty =>
      apply EqCtxEmpty
    | |- eqctx (ctxextend ?G ?A) (ctxextend ?D ?B) =>
      first [
          eapply EqCtxExtend ; magicn n try shelf true
        | apply CtxSym ; [
            eapply EqCtxExtend ; magicn n try shelf true
          | magicn n try shelf true ..
          ]
        ]
    | |- eqctx ?G ?G =>
      apply CtxRefl ; magicn n try shelf true
    | |- eqctx ?G ?D =>
      first [
        assumption
      | apply CtxSym ; [ assumption | magicn n try shelf true .. ]
      | cando shelf ; shelve
      ]
    (*! Equality of substitutions !*)
    | |- eqsubst (sbcomp sbweak (sbshift ?sbs)) (sbcomp ?sbs sbweak) ?G ?D =>
      eapply WeakNat ; magicn n try shelf true
    | |- eqsubst (sbcomp ?sbs sbweak) (sbcomp sbweak (sbshift ?sbs)) ?G ?D =>
      eapply SubstSym ; [
        eapply WeakNat ; magicn n try shelf true
      | magicn n try shelf true ..
      ]
    | |- eqsubst (sbcomp sbweak (sbzero ?u)) sbid ?G ?D =>
      eapply WeakZero ; magicn n try shelf true
    | |- eqsubst sbid (sbcomp sbweak (sbzero ?u)) ?G ?D =>
      eapply SubstSym ; [
        eapply WeakZero ; magicn n try shelf true
      | magicn n try shelf true ..
      ]
    | |- eqsubst (sbcomp (sbshift ?sbs) (sbzero (subst ?u ?sbs)))
                (sbcomp (sbzero ?u) ?sbs) ?G ?D =>
      eapply ShiftZero ; magicn n try shelf true
    | |- eqsubst (sbcomp (sbshift ?sbs) (sbzero ?v))
                (sbcomp (sbzero ?u) ?sbs) ?G ?D =>
      eapply @SubstTrans
      with (sb2 := sbcomp (sbshift sbs) (sbzero (subst u sbs))) ; [
        eapply CongSubstComp ; magicn n try shelf true
      | magicn n try shelf true ..
      ]
    | |- eqsubst (sbcomp (sbzero ?u) ?sbs)
                (sbcomp (sbshift ?sbs) (sbzero (subst ?u ?sbs))) ?G ?D =>
      eapply SubstSym ; [
        eapply ShiftZero ; magicn n try shelf true
      | magicn n try shelf true ..
      ]
    | |- eqsubst (sbzero ?u1) (sbzero ?u2) ?D ?E =>
      eapply CongSubstZero ; magicn n try shelf true
    | |- eqsubst sbweak sbweak ?D ?E =>
      eapply CongSubstWeak ; magicn n try shelf true
    | |- eqsubst (sbshift ?sbs1) (sbshift ?sbs2) ?D ?E =>
      first [
        eapply CongSubstShift ; magicn n try shelf true
      | eapply EqSubstCtxConv ; [
          eapply CongSubstShift ; magicn n try shelf true
        | magicn n try shelf true ..
        ]
      ]
    (* Basically copying stuff over from simplify... There should be a way
       to avoid that. *)
    | |- eqsubst (sbcomp sbweak (sbcomp (sbzero ?u) ?sbs)) ?sbt ?G ?D =>
      eapply SubstTrans ; [
        eapply SubstTrans ; [
          eapply CompAssoc
        | eapply CongSubstComp ; [
            idtac
          | eapply WeakZero
          | ..
          ]
        | ..
        ]
      | ..
      ] ; magicn n try shelf true
    | |- eqsubst (sbcomp (sbcomp sbweak (sbzero ?u)) ?sbs) ?sbt ?G ?D =>
      eapply SubstTrans ; [
        eapply CongSubstComp ; [
          idtac
        | eapply WeakZero
        | ..
        ]
      | ..
      ] ; magicn n try shelf true
    | |- eqsubst (sbcomp ?sbs (sbcomp sbweak (sbzero ?u))) ?sbt ?G ?D =>
      eapply SubstTrans ; [
        eapply CongSubstComp ; [
          eapply WeakZero
        | ..
        ]
      | ..
      ] ; magicn n try shelf true
    | |- eqsubst (sbcomp sbid ?sbs) ?sbt ?G ?D =>
      eapply SubstTrans ; [
        eapply CompIdLeft
      | ..
      ] ; magicn n try shelf true
    | |- eqsubst (sbcomp ?sbs sbid) ?sbt ?G ?D =>
      eapply SubstTrans ; [
        eapply CompIdRight
      | ..
      ] ; magicn n try shelf true
    (* This is a dangerous case. We need to take care of everything involving
       composition before this one. *)
    | |- eqsubst (sbcomp ?sb1 ?sb2) (sbcomp ?sb3 ?sb4) ?G ?D =>
      eapply CongSubstComp ; magicn n try shelf true
    | |- eqsubst ?sbs ?sbs ?G ?D =>
      eapply SubstRefl ; magicn n try shelf true
    | |- eqsubst ?sbs ?sbt ?G ?D =>
      tryif (is_var sbs ; is_var sbt)
      then first [
        eassumption
      | eapply SubstSym ; [ eassumption | magicn n try shelf true .. ]
      | eapply EqSubstCtxConv ; [ eassumption | magicn n try shelf true .. ]
      | eapply SubstSym ; [
          eapply EqSubstCtxConv ; [ eassumption | magicn n try shelf true .. ]
        | magicn n try shelf true ..
        ]
      ]
      (* Again we cheat a bit a repeat the _ case here. *)
      else (
        match eval compute in n with
        | 0 => assumption
        | S ?n => assumption || (constructor ; magicn n try shelf true)
        end
      )
    (* We should probably avoid using congruence on composition. *)
    (* To be continued... *)
    (*! Equality of types !*)
    | |- eqtype ?G (Subst (Subst ?A ?sbs) ?sbt) ?B =>
      compsubst1 ; magicn n try shelf true
    | |- eqtype ?G ?A (Subst (Subst ?B ?sbs) ?sbt) =>
      compsubst1 ; magicn n try shelf true
    (* A weird case perhaps. *)
    (* It feels like we should improve the case where is_var A and
       not is_var sbs below. *)
    | |- eqtype ?G (Subst ?B' (sbcomp ?sbs sbweak)) (Subst ?A (sbshift ?sbs)) =>
      tryif (is_evar A ; is_var B')
      then (
        eapply @EqTyTrans with (B := Subst (Subst B' sbweak) (sbshift sbs)) ; [
          idtac
        | eapply EqTyRefl
        | ..
        ] ; magicn n try shelf true
      )
      else eqtype_subst G (Subst B' (sbcomp sbs sbweak))
                        (Subst A (sbshift sbs))
                        magicn n try shelf tysym
    | |- eqtype ?G (Subst ?A (sbcomp (sbshift ?sbs) (sbzero (subst ?u ?sbs))))
                  (Subst ?B' ?sbs) =>
      tryif (is_evar A ; is_var B')
      then (
        eapply @EqTyTrans
        with (B := Subst (Subst B' sbweak)
                        (sbcomp (sbshift sbs) (sbzero (subst u sbs)))) ; [
          eapply EqTyRefl
        | ..
        ] ; magicn n try shelf true
      )
      else eqtype_subst G A (sbcomp (sbshift sbs) (sbzero (subst u sbs)))
                        (Subst B' sbs)
                        magicn n try shelf tysym
    | |- eqtype ?G (Subst ?A ?sbs) ?B =>
      (* We should push only if it makes sense. *)
      eqtype_subst G A sbs B magicn n try shelf tysym
    | |- eqtype ?G ?A (Subst ?B ?sbs) =>
      (* We know how to deal with the symmetric case. *)
      cando tysym ; eapply EqTySym ; [
        magicn n try shelf false
      | magicn n try shelf true ..
      ]
    | |- eqtype ?G (Id ?A ?u ?v) (Id ?B ?w ?z) =>
      eapply CongId ; magicn n try shelf true
    | |- eqtype ?G (Prod ?A ?B) (Prod ?C ?D) =>
      eapply CongProd ; magicn n try shelf true
    | |- eqtype ?G Bool Bool =>
      eapply EqTyRefl ; magicn n try shelf true
    | |- eqtype ?G ?A ?B =>
      (* We only want to catch the variable case, so we will copy the _ *)
      (* case here (it's a lazymatch). *)
      tryif (is_var A ; is_var B)
      then (
        first [
          eassumption
        | eapply EqTyRefl ; magicn n try shelf true
        | eapply EqTySym ; [ eassumption | magicn n try shelf true .. ]
        | eapply EqTyCtxConv ; [
            first [
              eassumption
            | eapply EqTySym ; [ eassumption | magicn n try shelf true .. ]
            ]
          | magicn n try shelf true ..
          ]
        ]
      )
      else (
        match eval compute in n with
        | 0 => assumption
        | S ?n => assumption || (constructor ; magicn n try shelf true)
        end
      )
    (* To be continued... *)
    (*! Equality of terms !*)
    | |- eqterm ?G (subst (subst ?u ?sbs) ?sbt) ?v ?A =>
      compsubst1 ; magicn n try shelf true
    | |- eqterm ?G ?u (subst (subst ?v ?sbs) ?sbt) ?A =>
      compsubst1 ; magicn n try shelf true
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
                eapply CongTermSubst ; magicn n try shelf true
              | eapply EqTyConv ; [
                  eapply CongTermSubst
                | ..
                ] ; magicn n try shelf true
              | eassumption
              ]
              else first [
                eapply EqSym ; [ simplify | .. ] ; magicn n try shelf true
              | eapply CongTermSubst ; magicn n try shelf true
              | eapply EqTyConv ; [
                  eapply CongTermSubst
                | ..
                ] ; magicn n try shelf true
              ]
            )
            else first [
              pushsubst1 ; magicn n try shelf true
            | eapply EqSym ; [ pushsubst1 | .. ] ; magicn n try shelf true
            | cando shelf ; shelve
            ]
          | _ =>
            first [
              eapply CongTermSubst ; magicn n try shelf true
            | eapply EqTyConv ; [
              eapply CongTermSubst
              | ..
              ] ; magicn n try shelf true
            | eassumption
            ]
          end
        )
        else first [
          simplify ; magicn n try shelf true
        | eapply CongTermSubst ; magicn n try shelf true
        | eapply EqTyConv ; [
            eapply CongTermSubst
          | ..
          ] ; magicn n try shelf true
        ]
      )
      else first [
        pushsubst1 ; magicn n try shelf true
      | cando shelf ; shelve
      ]
    | |- eqterm ?G ?u (subst ?v ?sbs) ?A =>
      (* We know how to deal with the symmetric case. *)
      (* We use the token tysym, maybe we should have some dedicated tmsym... *)
      cando tysym ; eapply EqSym ; [
        magicn n try shelf false
      | magicn n try shelf true ..
      ]
    | |- eqterm ?G ?u ?v ?A =>
      tryif (is_var u ; is_var v)
      then first [
        eassumption
      | eapply EqRefl ; magicn n try shelf true
      | eapply EqSym ; [
          eassumption
        | magicn n try shelf true ..
        ]
      | eapply EqTyConv ; [ eassumption | magicn n try shelf true .. ]
      | eapply EqTyConv ; [
          eapply EqSym ; [ eassumption | .. ]
        | ..
        ] ; magicn n try shelf true
      ]
      else (
          (* As always, this a temporary measure *)
        match eval compute in n with
        | 0 => assumption
        | S ?n => assumption || (constructor ; magicn n try shelf true)
        end
      )
    (* To be continued... *)
    (* When all else fails. *)
    (* This part will hopefully be gone at some point. *)
    (* And replaced by fail probably. *)
    | _ =>
      match eval compute in n with
      | 0 => assumption
      | S ?n => assumption || (constructor ; magicn n try shelf true)
      end
    end
  | cando try
  ].

Ltac magic2 := magicn (S (S 0)) false true true.
Ltac magic3 := magicn (S (S (S 0))) false true true.
Ltac magic4 := magicn (S (S (S (S 0)))) false true true.
Ltac magic5 := magicn (S (S (S (S (S 0))))) false true true.
Ltac magic := magic2.
Ltac trymagic := magicn (S (S 0)) true true true.
Ltac strictmagic := magicn (S (S 0)) false false true.

(* With it we improve compsubst1 *)
Ltac gocompsubst := compsubst1 ; try magic.

(* With it we improve pushsubst1 *)
Ltac gopushsubst := pushsubst1 ; try magic.
