Require config.
Require Import tt.

Section Ptt.

Local Instance hasPrecond : config.Precond := {| config.precondFlag := config.Yes |}.
Context {ConfigReflection : config.Reflection}.
Context {ConfigSimpleProducts : config.SimpleProducts}.
Context {ConfigProdEta : config.ProdEta}.
Context {ConfigUniverses : config.Universes}.
Context {ConfigWithProp : config.WithProp}.
Context {ConfigWithJ : config.WithJ}.
Context {ConfigEmpty : config.WithEmpty}.
Context {ConfigUnit : config.WithUnit}.
Context {ConfigBool : config.WithBool}.
Context {ConfigPi : config.WithPi}.

Context {ConfigSyntax : config.Syntax}.

Definition isctx := isctx.
Definition issubst := issubst.
Definition istype := istype.
Definition isterm := isterm.
Definition eqctx := eqctx.
Definition eqsubst := eqsubst.
Definition eqtype := eqtype.
Definition eqterm := eqterm.

End Ptt.
