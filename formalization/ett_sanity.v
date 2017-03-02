(* Sanity theorems for ett. *)

Require config.
Require Import config_tactics.


Require Import syntax.
Require Import tt.

Require ptt.
Require ptt_sanity.
Require Import ett.
Require Import ett2ptt ptt2ett.

Section EttSanity.

Context `{configReflection : config.Reflection}.

Theorem sane_issubst sbs G D :
  issubst sbs G D -> isctx G * isctx D.
Proof.
  intro h. split
  ; now apply ptt2ett.sane_isctx,
              (ptt_sanity.sane_issubst sbs G D),
              ett2ptt.sane_issubst.
Defined.

Theorem sane_istype G A :
  istype G A -> isctx G.
Proof.
  intro h.
  now apply ptt2ett.sane_isctx,
            (ptt_sanity.sane_istype G A),
            ett2ptt.sane_istype.
Defined.

Theorem sane_isterm G u A :
  isterm G u A -> isctx G * istype G A.
Proof.
  intro h. split.
  - now apply ptt2ett.sane_isctx,
              (ptt_sanity.sane_isterm G u A),
              ett2ptt.sane_isterm.
  - now apply ptt2ett.sane_istype,
              (ptt_sanity.sane_isterm G u A),
              ett2ptt.sane_isterm.
Defined.

Theorem sane_eqctx G D :
  eqctx G D -> isctx G * isctx D.
Proof.
  intro h. split
  ; now apply ptt2ett.sane_isctx,
              (ptt_sanity.sane_eqctx G D),
              ett2ptt.sane_eqctx.
Defined.

Theorem sane_eqtype G A B :
  eqtype G A B -> isctx G * istype G A * istype G B.
Proof.
  intro h.
  (repeat split)
  ; [ apply ptt2ett.sane_isctx | apply ptt2ett.sane_istype .. ]
  ; now apply (ptt_sanity.sane_eqtype G A B),
              ett2ptt.sane_eqtype.
Defined.

Theorem sane_eqsubst sbs sbt G D :
  eqsubst sbs sbt G D -> isctx G * isctx D * issubst sbs G D * issubst sbt G D.
Proof.
  intro h.
  (repeat split)
  ; [ apply ptt2ett.sane_isctx
    | apply ptt2ett.sane_isctx
    | apply ptt2ett.sane_issubst
    | apply ptt2ett.sane_issubst
    ]
  ; now apply (ptt_sanity.sane_eqsubst sbs sbt G D),
              ett2ptt.sane_eqsubst.
Defined.

Theorem sane_eqterm G u v A :
  eqterm G u v A -> isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  intro h.
  (repeat split)
  ; [ apply ptt2ett.sane_isctx
    | apply ptt2ett.sane_istype
    | apply ptt2ett.sane_isterm ..
    ]
  ; now apply (ptt_sanity.sane_eqterm G u v A),
              ett2ptt.sane_eqterm.
Defined.

End EttSanity.
