Require config.
Require Import tt.

Section Ptt.

Local Instance hasPrecond : config.Precond := {| config.precondFlag := config.Yes |}.
Context `{configReflection : config.Reflection}.

Definition isctx := isctx.
Definition issubst := issubst.
Definition istype := istype.
Definition isterm := isterm.
Definition eqctx := eqctx.
Definition eqsubst := eqsubst.
Definition eqtype := eqtype.
Definition eqterm := eqterm.

End Ptt.

