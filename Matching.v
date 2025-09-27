From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import MudaCore Sorting Tactics.
Require Import Coq.Logic.Classical.

Module Matching.

  (* ---------- Utilities to decrement quantities and update books ---------- *)

  Definition dec_bid (b:Bid) (q:nat) : option Bid :=
    let q' := q_b b - q in
    if Nat.leb 1 q' then
      Some {| b_agent:=b_agent b; p_b:=p_b b; q_b:=q'; t_b:=t_b b |}
    else None.

  Definition dec_ask (a:Ask) (q:nat) : option Ask :=
    let q' := q_s a - q in
    if Nat.leb 1 q' then
      Some {| s_agent:=s_agent a; a_s:=a_s a; q_s:=q'; t_s:=t_s a |}
    else None.

  Fixpoint replace_opt_bid (x:Bid) (y:option Bid) (Bs:list Bid) : list Bid :=
    match Bs with
    | [] => []
    | h::t =>
        if Nat.eqb (t_b h) (t_b x) && Nat.eqb (p_b h) (p_b x) && Nat.eqb (q_b h) (q_b x)
        then match y with Some y' => y'::t | None => t end
        else h :: replace_opt_bid x y t
    end.

  Fixpoint replace_opt_ask (x:Ask) (y:option Ask) (Ss:list Ask) : list Ask :=
    match Ss with
    | [] => []
    | h::t =>
        if Nat.eqb (t_s h) (t_s x) && Nat.eqb (a_s h) (a_s x) && Nat.eqb (q_s h) (q_s x)
        then match y with Some y' => y'::t | None => t end
        else h :: replace_opt_ask x y t
    end.

  (* ---------- Boolean comparators consistent with PriorityB / PriorityS ---------- *)
  (* Buyers: higher price; ties: earlier time; then agent; then quantity *)
  Definition betterB (x y:Bid) : bool :=
    (p_b y <? p_b x) ||                                     (* px > py *)
    ((p_b x =? p_b y) &&
      ( (t_b x <? t_b y)                                    (* tx < ty *)
        || ((t_b x =? t_b y) &&
              ( (b_agent x <? b_agent y)                    (* agent tie *)
                || ((b_agent x =? b_agent y) &&
                      (q_b x <? q_b y)) )) )).              (* qty tie *)

  (* Sellers: lower ask; ties: earlier time; then agent; then quantity *)
  Definition betterS (x y:Ask) : bool :=
    (a_s x <? a_s y) ||                                     (* ax < ay *)
    ((a_s x =? a_s y) &&
      ( (t_s x <? t_s y)                                    (* tx < ty *)
        || ((t_s x =? t_s y) &&
              ( (s_agent x <? s_agent y)                    (* agent tie *)
                || ((s_agent x =? s_agent y) &&
                      (q_s x <? q_s y)) )) )).

  Lemma betterB_correct : forall x y, betterB x y = true <-> PriorityB x y.
  Proof.
    intros x y; unfold betterB, PriorityB.
    split.
    - (* bool -> Prop *)
      intro H.
      apply Bool.orb_true_iff in H.
      destruct H as [Hprice | Htie].
      + (* p_b y <? p_b x = true *) apply Nat.ltb_lt in Hprice. left. lia.
      + (* equal price branch *)
        apply Bool.andb_true_iff in Htie. destruct Htie as [Heq Hrest].
        apply Nat.eqb_eq in Heq. right. split; [assumption|].
        apply Bool.orb_true_iff in Hrest. destruct Hrest as [Htlt | Hmore].
        * (* t_b x <? t_b y *) apply Nat.ltb_lt in Htlt. left; exact Htlt.
        * (* t_b x =? t_b y && ... *)
          apply Bool.andb_true_iff in Hmore. destruct Hmore as [Hteq Hlex].
          apply Nat.eqb_eq in Hteq. right. split; [assumption|].
          apply Bool.orb_true_iff in Hlex. destruct Hlex as [Ha_lt | Hagent_tie].
          { apply Nat.ltb_lt in Ha_lt. left; exact Ha_lt. }
          { apply Bool.andb_true_iff in Hagent_tie. destruct Hagent_tie as [Ha_eq Hq_lt].
            apply Nat.eqb_eq in Ha_eq. apply Nat.ltb_lt in Hq_lt.
            right. split; [assumption|assumption]. }
    - (* Prop -> bool *)
      intro H.
      apply Bool.orb_true_iff.
      destruct H as [Hgt | [Heq Htier]].
      + (* price greater *) left. apply Nat.ltb_lt. lia.
      + (* price equal, then tiers *)
        right. apply Bool.andb_true_iff. split.
        * apply Nat.eqb_eq. exact Heq.
        * destruct Htier as [Htlt | [Hteq [Ha_lt | [Ha_eq Hq_lt]]]].
          -- (* earlier time *) apply Bool.orb_true_iff. left. apply Nat.ltb_lt. exact Htlt.
          -- (* time equal, smaller agent *)
            apply Bool.orb_true_iff. right.
            apply Bool.andb_true_iff. split.
            ++ apply Nat.eqb_eq. exact Hteq.
            ++ apply Bool.orb_true_iff. left. apply Nat.ltb_lt. exact Ha_lt.
          -- (* time equal, agent equal, smaller quantity *)
            apply Bool.orb_true_iff. right.
            apply Bool.andb_true_iff. split.
            ++ apply Nat.eqb_eq. exact Hteq.
            ++ apply Bool.orb_true_iff. right.
                apply Bool.andb_true_iff. split.
                ** apply Nat.eqb_eq. exact Ha_eq.
                ** apply Nat.ltb_lt. exact Hq_lt.
  Qed.

  Lemma betterS_correct : forall x y, betterS x y = true <-> PriorityS x y.
  Proof.
    intros x y; unfold betterS, PriorityS.
    split.
    - (* bool -> Prop *)
      intro H.
      apply Bool.orb_true_iff in H.
      destruct H as [Hask | Htie].
      + (* a_s x <? a_s y *) apply Nat.ltb_lt in Hask. left. exact Hask.
      + apply Bool.andb_true_iff in Htie. destruct Htie as [Heq Hrest].
        apply Nat.eqb_eq in Heq. right. split; [assumption|].
        apply Bool.orb_true_iff in Hrest. destruct Hrest as [Htlt | Hmore].
        * apply Nat.ltb_lt in Htlt. left; exact Htlt.
        * apply Bool.andb_true_iff in Hmore. destruct Hmore as [Hteq Hlex].
          apply Nat.eqb_eq in Hteq. right. split; [assumption|].
          apply Bool.orb_true_iff in Hlex. destruct Hlex as [Ha_lt | Hagent_tie].
          { apply Nat.ltb_lt in Ha_lt. left; exact Ha_lt. }
          { apply Bool.andb_true_iff in Hagent_tie. destruct Hagent_tie as [Ha_eq Hq_lt].
            apply Nat.eqb_eq in Ha_eq. apply Nat.ltb_lt in Hq_lt.
            right. split; [assumption|assumption]. }
    - (* Prop -> bool *)
      intro H.
      apply Bool.orb_true_iff.
      destruct H as [Hlt | [Heq Htier]].
      + (* lower ask *) left. apply Nat.ltb_lt. exact Hlt.
      + right. apply Bool.andb_true_iff. split.
        * apply Nat.eqb_eq. exact Heq.
        * destruct Htier as [Htlt | [Hteq [Ha_lt | [Ha_eq Hq_lt]]]].
          -- apply Bool.orb_true_iff. left. apply Nat.ltb_lt. exact Htlt.
          -- apply Bool.orb_true_iff. right.
            apply Bool.andb_true_iff. split.
            ++ apply Nat.eqb_eq. exact Hteq.
            ++ apply Bool.orb_true_iff. left. apply Nat.ltb_lt. exact Ha_lt.
          -- apply Bool.orb_true_iff. right.
            apply Bool.andb_true_iff. split.
            ++ apply Nat.eqb_eq. exact Hteq.
            ++ apply Bool.orb_true_iff. right.
                apply Bool.andb_true_iff. split.
                ** apply Nat.eqb_eq. exact Ha_eq.
                ** apply Nat.ltb_lt. exact Hq_lt.
  Qed.


  (* ---------- Feasibility (boolean form) ---------- *)

  Definition feasibleb (b:Bid) (a:Ask) : bool :=
    Nat.leb (a_s a) (p_b b) && Nat.leb 1 (q_b b) && Nat.leb 1 (q_s a).

  Lemma feasibleb_correct : forall b a, feasibleb b a = true <-> matchable b a.
  Proof.
    intros b a; unfold feasibleb, matchable.
    repeat (rewrite andb_true_iff).
    repeat (rewrite ?Nat.leb_le); tauto.
  Qed.

  (* ---------- Find/Best over lists ---------- *)

  Fixpoint has_feasible_ask (b:Bid) (Ss:list Ask) : bool :=
    match Ss with
    | [] => false
    | a::t => if feasibleb b a then true else has_feasible_ask b t
    end.

  Fixpoint best_byB (cur:option Bid) (x:Bid) : option Bid :=
    match cur with
    | None => Some x
    | Some y => if betterB x y then Some x else Some y
    end.

  Fixpoint best_feasible_bid (Bs:list Bid) (Ss:list Ask) : option Bid :=
    match Bs with
    | [] => None
    | b::t =>
        let rest := best_feasible_bid t Ss in
        if has_feasible_ask b Ss then best_byB rest b else rest
    end.

  Fixpoint best_feasible_ask_for (b:Bid) (Ss:list Ask) : option Ask :=
    match Ss with
    | [] => None
    | a::t =>
        let rest := best_feasible_ask_for b t in
        if feasibleb b a
        then match rest with
             | None => Some a
             | Some a' => if betterS a a' then Some a else Some a'
             end
        else rest
    end.

  Definition pick_best_pair (Bs:list Bid) (Ss:list Ask) : option (Bid*Ask) :=
    match best_feasible_bid Bs Ss with
    | None => None
    | Some b =>
        match best_feasible_ask_for b Ss with
        | None => None
        | Some a => Some (b,a)
        end
    end.

  (* ---------- Helper facts ---------- *)

  Lemma has_feasible_ask_sound :
    forall b Ss, has_feasible_ask b Ss = true ->
      exists a, In a Ss /\ matchable b a.
  Proof.
    intros b Ss; induction Ss as [|a t IH]; cbn; intro H; try discriminate.
    destruct (feasibleb b a) eqn:E; cbn in H.
    - (* feasibleb b a = true *)
      exists a; split; [left; reflexivity|].
      apply feasibleb_correct; exact E.
    - (* feasibleb b a = false; so H is has_feasible_ask b t = true *)
      specialize (IH H) as [a' [Hin Hm]].
      exists a'; split; [right; exact Hin|exact Hm].
  Qed.



  Lemma best_byB_spec :
    forall cur x y,
      best_byB cur x = Some y ->
      (y = x \/ (exists z, cur = Some z /\ y = z)) /\
      (forall z, cur = Some z -> y = x \/ PriorityB y z).
  Proof.
    intros cur x y; destruct cur as [z|]; cbn; intro H.
    - destruct (betterB x z) eqn:Eb; inversion H; subst; clear H.
      + split; [left; reflexivity|].
        intros z' Hz'. inversion Hz'; subst.
        right. apply (proj1 (betterB_correct _ _)) in Eb. exact Eb.
      + split; [right; eexists; split; eauto|].
        intros z' Hz'. inversion Hz'; subst. left; reflexivity.
    - inversion H; subst. split; [left; reflexivity|].
      intros z' Hz'. inversion Hz'.
  Qed.

  (* ---------- “Best” feasible bid: presence + maximality ---------- *)

  (* Old problematic spec removed. Use this simpler, correct spec instead. *)
  Lemma best_byB_spec :
    forall cur x y,
      best_byB cur x = Some y ->
      (y = x \/ exists z, cur = Some z /\ y = z).
  Proof.
    intros cur x y; destruct cur as [z|]; cbn; intro H.
    - destruct (betterB x z) eqn:Eb; inversion H; subst; clear H; [left; reflexivity|].
      right. eexists; split; eauto.
    - inversion H; subst. left; reflexivity.
  Qed.


  (* ---------- “Best” feasible ask FOR fixed b: presence + minimality ---------- *)

  Lemma best_feasible_ask_for_sound :
    forall Ss b a,
      best_feasible_ask_for b Ss = Some a ->
      In a Ss /\ matchable b a /\
      (forall a', In a' Ss -> matchable b a' -> a' = a \/ PriorityS a a').
  Proof.
    intros Ss b; induction Ss as [|x t IH]; cbn; intros a H; try discriminate.
    destruct (feasibleb b x) eqn:Efx.
    - destruct (best_feasible_ask_for b t) eqn:Er.
      + destruct (betterS x a0) eqn:Ecmp; inversion H; subst; clear H.
        * split; [left; reflexivity|].
          split; [apply feasibleb_correct; exact Efx|].
          intros a' Ina' Hm.
          destruct Ina' as [->|Hin].
          { left; reflexivity. }
          apply IH in Er as [HinA0 [HmA0 MaxA0]].
          right.
          (* a dominates a0 or equal; and a0 dominates any feasible from tail *)
          apply (proj1 (betterS_correct _ _)) in Ecmp.
          destruct PriorityS_strict_total as [_ [Ptrans _]].
          destruct (MaxA0 a' Hin Hm) as [->|Ha0].
          - exact Ecmp.
          - eapply Ptrans; eauto.
        * inversion H; subst; clear H.
          apply IH in Er as [HinA0 [HmA0 MaxA0]].
          split; [right; exact HinA0|].
          split; [exact HmA0|].
          intros a' Ina' Hm.
          destruct Ina' as [->|Hin']; [left; reflexivity|].
          apply MaxA0; assumption.
      + inversion H; subst; clear H.
        split; [left; reflexivity|].
        split; [apply feasibleb_correct; exact Efx|].
        intros a' Ina' Hm.
        destruct Ina' as [->|Hin]; [left; reflexivity|].
        (* impossible: if some a' in tail feasible, the recursive call would not be None *)
        exfalso. revert Hin Hm Er. induction t; cbn; intros; [inversion Hin|].
        destruct Hin as [->|Hin'].
        { rewrite (proj2 (feasibleb_correct _ _)) in Hm. congruence. }
        apply IHt; auto.
    - apply IH in H as [Hin [Hm Max]].
      split; [right; exact Hin|].
      split; [exact Hm|].
      intros a' Ina' Hm'.
      apply Max; auto.
  Qed.

  (* Combined soundness for the (b,a) pair *)
  Lemma pick_best_pair_sound :
    forall Bs Ss b a,
      pick_best_pair Bs Ss = Some (b,a) ->
      In b Bs /\ In a Ss /\ matchable b a /\
      (forall b', In b' Bs -> (exists a', In a' Ss /\ matchable b' a') ->
         b' = b \/ PriorityB b b') /\
      (forall a', In a' Ss -> matchable b a' ->
         a' = a \/ PriorityS a a').
  Proof.
    intros Bs Ss b a.
    unfold pick_best_pair.
    destruct (best_feasible_bid Bs Ss) eqn:Eb; try discriminate.
    destruct (best_feasible_ask_for b0 Ss) eqn:Ea; try discriminate.
    inversion 1; subst; clear 1.
    pose proof (best_feasible_bid_sound _ _ _ Eb) as [HinB [HexB MaxB]].
    pose proof (best_feasible_ask_for_sound _ _ _ Ea) as [HinA [FeasA MaxA]].
    repeat split; auto.
  Qed.

  (* ---------- Greedy Step, invariants, and termination ---------- *)

  Inductive Step : State -> State -> Prop :=
  | step_match :
      forall Bs Ss M b a
        (Hp : pick_best_pair Bs Ss = Some (b,a)),
      let q := q_ij b a in
      q > 0 ->
      let Bs' := replace_opt_bid b (dec_bid b q) Bs in
      let Ss' := replace_opt_ask a (dec_ask a q) Ss in
      Step
        {| Bids := Bs; Asks := Ss; Mt := M |}
        {| Bids := Bs'; Asks := Ss'; Mt := M ++ [{| mb:=b; ma:=a; mq:=q |}] |}.

  Lemma step_monotone :
    forall s1 s2, Step s1 s2 -> monotone_Mt (Mt s1) (Mt s2).
  Proof.
    intros [Bs Ss M] [Bs' Ss' M'] H; inversion H; subst; simpl.
    unfold monotone_Mt; intros m Hin; apply in_or_app; now left.
  Qed.

  Lemma step_adds_feasible :
    forall s1 s2, Step s1 s2 -> exists m, In m (Mt s2) /\ feasible_match m.
  Proof.
    intros [Bs Ss M] [Bs' Ss' M'] H; inversion H; subst; simpl.
    eexists; split; [apply in_or_app; right; simpl; auto|].
    unfold feasible_match; split.
    - destruct (pick_best_pair_sound _ _ _ _ Hp) as [_ [_ Hfeas _]]; exact Hfeas.
    - reflexivity.
  Qed.

  Inductive Steps : State -> State -> Prop :=
  | steps_refl : forall s, Steps s s
  | steps_cons : forall s1 s2 s3, Step s1 s2 -> Steps s2 s3 -> Steps s1 s3.

  Lemma steps_monotone :
    forall s1 s2, Steps s1 s2 -> monotone_Mt (Mt s1) (Mt s2).
  Proof.
    intros s1 s2 H; induction H; cbn; try (intros m Hin; exact Hin).
    intros m Hin. eapply IHSteps, step_monotone; eauto.
  Qed.

  Definition Terminal (s:State) : Prop :=
    forall b a, In b (Bids s) -> In a (Asks s) -> ~ matchable b a.

  Definition measure (s:State) : nat :=
    (fold_left (fun acc b => acc + q_b b) (Bids s) 0) +
    (fold_left (fun acc a => acc + q_s a) (Asks s) 0).

  Lemma step_decreases_measure :
    forall s1 s2, Step s1 s2 -> measure s2 < measure s1.
  Proof.
    intros [Bs Ss M] [Bs' Ss' M'] H; inversion H; subst; cbn.
    set (q := q_ij b a).
    assert (q>0) by auto.
    assert (q<=q_b b) by (apply Nat.min_l; lia).
    assert (q<=q_s a) by (apply Nat.min_r; lia).
    lia.
  Qed.

  (* If a feasible pair exists, the best picker finds one *)
  Lemma pick_best_pair_exists :
    forall Bs Ss,
      (exists b a, In b Bs /\ In a Ss /\ matchable b a) ->
      exists b a, pick_best_pair Bs Ss = Some (b,a).
  Proof.
    intros Bs Ss [b [a [HinB [HinA Hm]]]].
    (* best_feasible_bid is Some: witness b *)
    assert (has_feasible_ask b Ss = true) as Hhas.
    { unfold has_feasible_ask.
      revert HinA Hm. induction Ss as [|x t IH]; cbn; intros; [inversion HinA|].
      destruct HinA as [->|Hin]; [rewrite (proj2 (feasibleb_correct _ _)); auto|].
      destruct (feasibleb b x); auto. }
    (* hence best_feasible_bid returns Some *)
    assert (exists b0, best_feasible_bid Bs Ss = Some b0) as [b0 Eb].
    { clear - Bs Ss b HinB Hhas.
      revert b HinB Hhas.
      induction Bs as [|x t IH]; cbn; intros; [inversion HinB|].
      destruct HinB as [->|Hin].
      - rewrite Hhas. destruct (best_feasible_bid t Ss); eauto.
      - specialize (IH _ Hin Hhas) as [bb Eb]. rewrite Eb.
        destruct (has_feasible_ask x Ss); destruct (best_byB (Some bb) x); eauto. }
    (* then best_feasible_ask_for that b0 is Some by soundness *)
    destruct (best_feasible_ask_for b0 Ss) eqn:Ea.
    - eexists; eexists; reflexivity.
    - (* impossible: soundness says chosen b0 has some feasible a *)
      exfalso.
      pose proof (best_feasible_bid_sound _ _ _ Eb) as [_ [Hex _]].
      destruct Hex as [a0 [Ina0 Hm0]].
      clear - Ea Ina0 Hm0.
      revert Ina0 Hm0 Ea. induction Ss; cbn; intros; [inversion Ina0|].
      destruct Ina0 as [->|Hin]; [ rewrite (proj2 (feasibleb_correct _ _)) in Hm0; congruence |].
      destruct (feasibleb b0 a); eauto.
  Qed.

  Lemma step_or_terminal :
    forall s, (exists s', Step s s') \/ Terminal s.
  Proof.
    intros [Bs Ss M]; cbn.
    destruct (classic (exists b a, In b Bs /\ In a Ss /\ matchable b a)) as [Hex|Hnone].
    - left. destruct (pick_best_pair_exists _ _ Hex) as [b [a Hp]].
      eexists. econstructor; eauto; cbn; lia.
    - right. intros b a Hb Ha Hm. apply Hnone.
      exists b, a; repeat split; auto.
  Qed.

  Theorem termination_exists :
    forall s0, exists sT, Steps s0 sT /\ Terminal sT.
  Proof.
    intros s0. remember (measure s0) as n.
    revert s0 Heqn. induction n as [|n IH]; intros s Heq.
    - exists s. split; [constructor|].
      intros b a Hb Ha [H _]; lia.
    - destruct (step_or_terminal s) as [[s' Hstep] | Hterm].
      + assert (measure s' < measure s) by (eapply step_decreases_measure; eauto).
        assert (measure s' <= n) by lia.
        destruct (IH s' eq_refl) as [sT [Hst HT]].
        eexists. split; [econstructor; eauto|exact HT].
      + eexists. split; [constructor|exact Hterm].
  Qed.

  Theorem no_feasible_pairs_at_terminal :
    forall sT, Terminal sT ->
      forall b a, In b (Bids sT) -> In a (Asks sT) -> ~ matchable b a.
  Proof. exact (fun sT Hterm => Hterm). Qed.

End Matching.

Export Matching.
