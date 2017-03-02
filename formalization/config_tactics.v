Require Import config.

(* Deal with configuration. *)
Ltac doConfig :=
  (* configure the goal *)
  match goal with
  | |- ?P -> ?Q =>
    match (eval cbv in P) with
    | Yes => intros _
    | No => let H := fresh "H" in (intros H ; now elim H)
    | precondFlag =>
      let H := fresh "precondFlag" in intros H
    | reflectionFlag =>
      let H := fresh "reflectionFlag" in intros H
    | _ => idtac
    end
  | _ => idtac
  end ;
  (* Configure the hypotheses *)
  repeat
  (match goal with
   | H : ?P -> ?Q |- _ =>
     match (eval cbv in P) with
     | Yes => specialize (H yes)
     | No => clear H
     | @precondFlag ?F =>
       match goal with
       | R : @precondFlag F |- _ => specialize (H R)
       end
     | @reflectionFlag ?F =>
       match goal with
       | R : @reflectionFlag F |- _ => specialize (H R)
       end
     end
   | _ => idtac
  end).

(* Perform a tactic and deal with a configuration. *)
Tactic Notation (at level 0) "config" tactic(t) := doConfig ; t ; doConfig.

Tactic Notation (at level 5) "capply" uconstr(H) := doConfig ; apply H ; doConfig.

Tactic Notation (at level 5) "ceapply" uconstr(H) := doConfig ; eapply H ; doConfig.
