From stdpp Require Export ssreflect.
From myiris.prelude Require Import options.

(** Iris itself and many dependencies still rely on this coercion. *)
Coercion Z.of_nat : nat >-> Z.
