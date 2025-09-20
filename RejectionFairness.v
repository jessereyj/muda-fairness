From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module RejectionFairness.

  (* Agent-level membership via association predicates *)
  Definition in_dom (M:list Match) (b:Bid) : Prop :=
    exists m, In m M /\ uses_bid_of m b.

  Definition in_codom (M:list Match) (a:Ask) : Prop :=
    exists m, In m M /\ uses_ask_of m a.

  Theorem rejection_fairness_terminal :
    forall s0 sT,
      Steps s0 sT -> Terminal sT ->
      (* Buyer-side: quantify b ∈ Bids sT, then say: if b not in dom(Mt), b has no feasible seller *)
      (forall b, In b (Bids sT) -> ~ in_dom (Mt sT) b ->
        forall a, In a (Asks sT) -> ~ matchable b a) /\
      (* Seller-side: symmetric *)
      (forall a, In a (Asks sT) -> ~ in_codom (Mt sT) a ->
        forall b, In b (Bids sT) -> ~ matchable b a).
  Proof.
    intros s0 sT Hst Ht.
    split.
    - (* Buyer-side branch *)
      intros b Hb _ a Ha.
      eapply no_feasible_pairs_at_terminal; eauto.
    - (* Seller-side branch *)
      intros a Ha _ b Hb.
      eapply no_feasible_pairs_at_terminal; eauto.
  Qed.


End RejectionFairness.

Export RejectionFairness.
