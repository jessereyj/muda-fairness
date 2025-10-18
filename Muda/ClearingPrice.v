From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module ClearingPrice.

  (* Clearing price - Definition 3.1.9 *)
  Definition clearing_price (s:State) : option nat :=
    match marginal_pair s with
    | None => None
    | Some (b, a, exhaustion) =>
        match exhaustion with
        | BuyerExhausted => Some (p_b b)    (* Buyer exhausted -> use bid *)
        | SellerExhausted => Some (a_s a)   (* Seller exhausted -> use ask *)
        | BothExhausted => Some (p_b b)     (* Both exhausted -> use bid *)
        end
    end.

  (* Clearing price bounds - Lemma 4.2.4 *)
  Lemma clearing_price_bounds :
    forall s b a ex,
      marginal_pair s = Some (b, a, ex) ->
      matchable b a ->
      match clearing_price s with
      | Some c => a_s a <= c <= p_b b
      | None => False
      end.
  Proof.
    intros s b a ex Hmarg Hfeas.
    unfold clearing_price. rewrite Hmarg.
    destruct ex; simpl; destruct Hfeas as [Hge _]; lia.
  Qed.

  (* Clearing price uniqueness *)
  Lemma clearing_price_unique :
    forall s c1 c2,
      clearing_price s = Some c1 ->
      clearing_price s = Some c2 ->
      c1 = c2.
  Proof.
    intros s c1 c2 H1 H2.
    rewrite H1 in H2. inversion H2. reflexivity.
  Qed.

End ClearingPrice.

Export ClearingPrice.