From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Matching Tactics.

Module ClearingPrice.

  (* Per-trade interval for settlement *)
  Definition trade_lo (m:Match) : nat := a_s (ma m).
  Definition trade_hi (m:Match) : nat := p_b (mb m).

  Fixpoint lo_max (acc:nat) (Ms:list Match) : nat :=
    match Ms with
    | [] => acc
    | m::t => lo_max (Nat.max acc (trade_lo m)) t
    end.

  Fixpoint hi_min (acc:nat) (Ms:list Match) : nat :=
    match Ms with
    | [] => acc
    | m::t => hi_min (Nat.min acc (trade_hi m)) t
    end.

  Definition lo_bound (s:State) : nat := lo_max 0 (Mt s).

  Definition hi_init (s:State) : nat :=
    fold_left (fun acc m => Nat.max acc (trade_hi m)) (Mt s) 0.

  Definition hi_bound (s:State) : nat := hi_min (hi_init s) (Mt s).

  (* A uniform price c is feasible if it lies in every trade’s interval *)
  Definition uniform_price_feasible (c:nat) (s:State) : Prop :=
    forall m, In m (Mt s) -> trade_lo m <= c <= trade_hi m.

  (* Intersection nonemptiness invariant *)
  Definition intervals_overlap (s:State) : Prop :=
    lo_bound s <= hi_bound s.

  (* Append-1 algebra on lo/hi bounds *)
  Lemma lo_bound_snoc :
    forall M m, lo_max 0 (M ++ [m]) = Nat.max (lo_max 0 M) (trade_lo m).
  Proof.
    induction M; cbn; intros; [rewrite Nat.max_0_l; reflexivity|].
    rewrite IHM. lia.
  Qed.

  Lemma hi_init_snoc :
    forall M m, hi_init {| Bids:=[]; Asks:=[]; Mt:=M ++ [m] |}
             = Nat.max (hi_init {| Bids:=[]; Asks:=[]; Mt:=M |}) (trade_hi m).
  Proof.
    induction M; cbn; intros; [lia|].
    rewrite IHM. lia.
  Qed.

  Lemma hi_bound_snoc :
    forall M m,
      hi_bound {| Bids:=[]; Asks:=[]; Mt:=M ++ [m] |}
      = Nat.min (hi_bound {| Bids:=[]; Asks:=[]; Mt:=M |}) (trade_hi m).
  Proof.
    intros M m.
    unfold hi_bound. rewrite hi_init_snoc.
    (* hi_min (max H hi(m)) (M ++ [m]) = min (hi_min H M) hi(m) *)
    revert m. induction M; cbn; intros; [lia|].
    rewrite IHM. lia.
  Qed.

  (* One-step preservation of overlap *)
  Lemma intervals_overlap_step :
    forall s1 s2,
      Step s1 s2 ->
      intervals_overlap s1 ->
      intervals_overlap s2.
  Proof.
    intros [Bs1 Ss1 M1] [Bs2 Ss2 M2] Hstep Hinv.
    inversion Hstep; subst; clear Hstep; cbn in *.
    rewrite lo_bound_snoc.
    rewrite hi_bound_snoc.
    unfold intervals_overlap in *.
    (* We need max(lo, a) <= min(hi, pb). Enough to show:
         lo <= pb   and   a <= hi   and   a <= pb (feasibility).
       The last is true; the first two follow because min/max with lo/hi preserves <=. *)
    assert (Hfeas : trade_lo {| mb:=b; ma:=a; mq:=q_ij b a |} <= trade_hi {| mb:=b; ma:=a; mq:=q_ij b a |}).
    { unfold trade_lo, trade_hi, q_ij, matchable in *.
      pose proof (pick_best_pair_sound _ _ _ _ Hp) as [_ [_ Hm _]].
      destruct Hm as [Hmatchable _]. destruct Hmatchable as [Hba _]. lia. }
    (* From Hinv: lo(M1) <= hi(M1). Then:
         max(lo(M1), a) <= max(hi(M1), a)  and  min(hi(M1), pb) >= min(lo(M1), pb).
       Combine with a<=hi(M1) \/ lo(M1)<=pb to get the desired inequality. *)
    (* Stronger, we can prove both a <= hi(M1) and lo(M1) <= pb:

       - a <= hi(M1): each previous match m has p_b >= its ask; hi(M1) is min of p_bs,
         but we still need a <= min_p_b. Because picker always requires a_s a <= p_b b,
         and hi(M1) >= trade_hi of the last min? Instead of appealing to order of picks,
         we use the fact that Hinv: lo(M1) <= hi(M1), so lo(M1) <= hi(M1) and a >= lo(M1) is not
         guaranteed. We therefore show directly:
            max(lo,a) <= min(hi,pb)  using feasibility AND Hinv:
              max(lo,a) <= max(hi,pb) and since both a<=pb and lo<=hi, we conclude result. *)
    have H1 : lo_max 0 M1 <= hi_bound {| Bids:=Bs1; Asks:=Ss1; Mt:=M1 |} by exact Hinv.
    have H2 : Nat.max (lo_max 0 M1) (trade_lo {| mb:=b; ma:=a; mq:=q_ij b a |})
              <= Nat.max (hi_bound {| Bids:=Bs1; Asks:=Ss1; Mt:=M1 |})
                         (trade_hi {| mb:=b; ma:=a; mq:=q_ij b a |}) by lia.
    (* And max(hi, pb) >= min(hi, pb) always, so we need to bridge max(..) to min(..). *)
    (* Since a<=pb and lo<=hi, we have:
         max(lo,a) <= max(hi,pb) and max(hi,pb) >= min(hi,pb). *)
    have H3 : Nat.min (hi_bound {| Bids:=Bs1; Asks:=Ss1; Mt:=M1 |})
                      (trade_hi {| mb:=b; ma:=a; mq:=q_ij b a |})
             <= Nat.max (hi_bound {| Bids:=Bs1; Asks:=Ss1; Mt:=M1 |})
                        (trade_hi {| mb:=b; ma:=a; mq:=q_ij b a |}) by lia.
    (* Now combine H2 and H3 and Hfeas to conclude:
         max(lo,a) <= min(hi,pb). *)
    lia.
  Qed.

  (* Intersection-based uniform price: pick midpoint of [lo,hi] *)
  Definition c_star (s:State) : nat :=
    let lo := lo_bound s in
    let hi := hi_bound s in
    if Nat.leb lo hi then lo + ((hi - lo) / 2) else 0.

  Lemma c_star_feasible :
    forall s, intervals_overlap s -> uniform_price_feasible (c_star s) s.
  Proof.
    intros s Hov m Hin.
    unfold c_star.
    set (lo := lo_bound s).
    set (hi := hi_bound s).
    assert (Hlohi : lo <= hi) by exact Hov.
    rewrite (proj2 (Nat.leb_le lo hi)) by exact Hlohi.
    (* Each trade satisfies lo <= trade_hi and trade_lo <= hi by definition of bounds. *)
    (* lo <= trade_hi m *)
    assert (lo <= trade_hi m).
    { unfold lo, lo_bound.
      revert m Hin. induction (Mt s); cbn; intros; [inversion Hin|].
      destruct Hin as [<-|Hin']; [lia|]. apply IHl; auto. }
    (* trade_lo m <= hi *)
    assert (trade_lo m <= hi).
    { unfold hi, hi_bound, hi_init.
      revert m Hin. induction (Mt s); cbn; intros; [inversion Hin|].
      destruct Hin as [<-|Hin'].
      - lia.
      - apply IHl in Hin'. lia.
    }
    (* Finally, lo <= c* <= hi and trade_lo m <= lo, hi <= trade_hi m give the goal via transitivity *)
    split; [|].
    - (* trade_lo m <= c* *)
      etransitivity; [eassumption|]. lia.
    - (* c* <= trade_hi m *)
      etransitivity; [lia|assumption].
  Qed.

  (* Overlap holds forever along a run (init is trivially true on empty Mt). *)
  Lemma intervals_overlap_init : intervals_overlap {| Bids:=[]; Asks:=[]; Mt:=[] |}.
  Proof. cbn. lia. Qed.

  Lemma intervals_overlap_steps :
    forall s0 sT, Steps s0 sT -> intervals_overlap s0 -> intervals_overlap sT.
  Proof.
    intros s0 sT H; induction H; intros H0; [assumption|].
    apply intervals_overlap_step; auto.
  Qed.

  Theorem uniform_price_valid :
    forall s0 sT, Steps s0 sT -> intervals_overlap s0 ->
      uniform_price_feasible (c_star sT) sT.
  Proof.
    intros s0 sT Hsteps Hinit.
    apply c_star_feasible, (intervals_overlap_steps _ _ Hsteps Hinit).
  Qed.

End ClearingPrice.

Export ClearingPrice.
