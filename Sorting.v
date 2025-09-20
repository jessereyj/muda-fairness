From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore.

Module Sorting.
  (* Priority relations (Def. 3.1.4) as abstract strict total orders 
     consistent with price-time (you may replace by concrete defs later). *)
  Parameter PriorityB : Bid -> Bid -> Prop.
  Parameter PriorityS : Ask -> Ask -> Prop.

  Axiom PriorityB_strict_total :
    (forall x, ~ PriorityB x x) /\
    (forall x y z, PriorityB x y -> PriorityB y z -> PriorityB x z) /\
    (forall x y, x <> y -> PriorityB x y \/ PriorityB y x).

  Axiom PriorityS_strict_total :
    (forall x, ~ PriorityS x x) /\
    (forall x y z, PriorityS x y -> PriorityS y z -> PriorityS x z) /\
    (forall x y, x <> y -> PriorityS x y \/ PriorityS y x).

  (* Documentation lemmas: consistent with price-time rule *)
  Axiom PriorityB_price_time:
    forall b1 b2,
      p_b b1 > p_b b2 \/ (p_b b1 = p_b b2 /\ t_b b1 < t_b b2) ->
      PriorityB b1 b2.

  Axiom PriorityS_price_time:
    forall a1 a2,
      a_s a1 < a_s a2 \/ (a_s a1 = a_s a2 /\ t_s a1 < t_s a2) ->
      PriorityS a1 a2.
End Sorting.

Export Sorting.
