From Coq Require Import List Arith Lia.
Import ListNotations.

Ltac crush := repeat (simpl in *; subst; intuition; try lia).