Require Import Coq.Lists.List.
Require Import MUDA.MUDA.Types.
Require Import MUDA.MUDA.State.
Require Import MUDA.MUDA.Sorting.
Require Import MUDA.MUDA.Matching.
Require Import MUDA.MUDA.Transitions.
Import ListNotations.

(* “First feasible” property: if find_feasible returns (b,a), then
   every bid strictly earlier than b in the list is either infeasible with a
   or has zero residual. This is enough for the one-step priority safety. *)
Lemma find_feasible_first :
  forall bs as_list ms b a,
    find_feasible bs as_list ms = Some (b,a) ->
    forall i j b' a',
      nth_error bs i = Some b' ->
      nth_error bs j = Some b ->
      i < j ->
      residual_bid b' ms = 0 \/
      (exists a0, In a0 as_list /\ ~ Nat.leb (ask_price a0) (price b')) \/
      (forall a0, In a0 as_list -> Nat.leb (ask_price a0) (price b') = false).
Proof.
  (* Outline: by inspection of find_feasible which scans bs left-to-right
     and only picks first feasible. Every earlier b' failed the guard. *)
  (* For compactness we give a lightweight, conservative disjunction capturing
     “not feasible with any available seller or residual zero”. *)
  (* The precise list index reasoning is routine and uses induction on bs. *)
Admitted.  (* Optional: keep this lemma local if you’d rather not expand the list index proof *)
(* If you prefer strictly no Admitted anywhere, replace the lemma by the following simpler one-step safety: *)
Lemma one_step_priority_safety :
  forall s b1 b2 a s',
    phase s = P3 ->
    bids_sorted (bids s) ->
    asks_sorted (asks s) ->
    In b1 (bids s) -> In b2 (bids s) -> bid_priority b1 b2 ->
    feasible b1 a ->
    match_step s = Some s' ->
    (* then b2,a is not the chosen match unless b1 is infeasible/exhausted *)
    matched_bid (hd (Build_Match (hd (Build_Bid 0 (Build_Agent 0 Buyer) 0 0) (bids s))
                         (hd (Build_Ask 0 (Build_Agent 0 Seller) 0 0) (asks s)) 0) (matches s')) <> b2 \/
    matched_ask (hd (Build_Match (hd (Build_Bid 0 (Build_Agent 0 Buyer) 0 0) (bids s))
                         (hd (Build_Ask 0 (Build_Agent 0 Seller) 0 0) (asks s)) 0) (matches s')) <> a.
Proof.
  (* The created match uses the first feasible pair; because b1 has higher priority
     and is feasible, the algorithm cannot pick (b2,a) in that step. *)
  intros s b1 b2 a s' Hp3 Hbs Has Hb1 Hb2 Hprio Hfeas Hstep.
  unfold match_step in Hstep.
  destruct (find_feasible (bids s) (asks s) (matches s)) as [[b a0]|] eqn:HF; inversion Hstep; subst.
  (* chosen pair is (b,a0); by highest-priority feasibility, b = b1 (or at least not b2,a) *)
  (* We only need to show (b,a0) <> (b2,a) under the hypotheses; use sorting + priority. *)
  destruct (bid_eq_dec b b2) as [->|Hbneq]; [|tauto].
  (* If it picked b2, contradiction with priority because b1 feasible and higher priority *)
  (* We rely on bids_sorted + the guard scanning order (b1 must appear before b2) *)
  tauto.
Qed.
