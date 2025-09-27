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

  Definition betterB (x y:Bid) : bool :=
    (p_b y <? p_b x) ||
    ((p_b x =? p_b y) &&
      ((t_b x <? t_b y) ||
        ((t_b x =? t_b y) &&
          ((b_agent x <? b_agent y) ||
            ((b_agent x =? b_agent y) &&
              (q_b x <? q_b y)))))).

  Definition betterS (x y:Ask) : bool :=
    (a_s x <? a_s y) ||
    ((a_s x =? a_s y) &&
      ((t_s x <? t_s y) ||
        ((t_s x =? t_s y) &&
          ((s_agent x <? s_agent y) ||
            ((s_agent x =? s_agent y) &&
              (q_s x <? q_s y)))))).

  Lemma betterB_correct : forall x y, betterB x y = true <-> PriorityB x y.
  Proof.
    intros x y; unfold betterB, PriorityB.
    split.
    - intro H. apply Bool.orb_true_iff in H.
      destruct H as [Hlt|Hrest].
      + apply Nat.ltb_lt in Hlt. left. lia.
      + apply Bool.andb_true_iff in Hrest. destruct Hrest as [Heq Htier].
        apply Nat.eqb_eq in Heq. right. split; [exact Heq|].
        apply Bool.orb_true_iff in Htier. destruct Htier as [Htlt|Hmore].
        * apply Nat.ltb_lt in Htlt. left; exact Htlt.
        * apply Bool.andb_true_iff in Hmore. destruct Hmore as [Hteq Hlex].
          apply Nat.eqb_eq in Hteq. right. split; [exact Hteq|].
          apply Bool.orb_true_iff in Hlex. destruct Hlex as [Ha_lt|Hagent_eq].
          -- apply Nat.ltb_lt in Ha_lt. left; exact Ha_lt.
          -- apply Bool.andb_true_iff in Hagent_eq. destruct Hagent_eq as [Ha_eq Hq_lt].
             apply Nat.eqb_eq in Ha_eq. apply Nat.ltb_lt in Hq_lt.
             right. split; [exact Ha_eq|exact Hq_lt].
    - intro H. apply Bool.orb_true_iff.
      destruct H as [Hprice|[Heq Htier]].
      + left. apply Nat.ltb_lt. exact Hprice.
      + right. apply Bool.andb_true_iff. split.
        * apply Nat.eqb_eq. exact Heq.
        * destruct Htier as [Htlt|[Hteq [Ha_lt|[Ha_eq Hq_lt]]]].
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

  Definition feasibleb (b:Bid) (a:Ask) : bool :=
    Nat.leb (a_s a) (p_b b) && Nat.leb 1 (q_b b) && Nat.leb 1 (q_s a).

  Lemma feasibleb_correct : forall b a, feasibleb b a = true <-> matchable b a.
  Proof.
    intros b a; unfold feasibleb, matchable.
    repeat rewrite andb_true_iff.
    repeat rewrite ?Nat.leb_le.
    tauto.
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
        let r := best_feasible_bid t Ss in
        if has_feasible_ask b Ss then best_byB r b else r
    end.

  Fixpoint best_feasible_ask_for (b:Bid) (Ss:list Ask) : option Ask :=
    match Ss with
    | [] => None
    | a::t =>
        let r := best_feasible_ask_for b t in
        if feasibleb b a
        then match r with
             | None => Some a
             | Some a' => if betterS a a' then Some a else Some a'
             end
        else r
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

    Lemma best_byB_spec :
      forall cur x y,
        best_byB cur x = Some y ->
        (y = x \/ exists z, cur = Some z /\ y = z).
    Proof.
      intros cur x y H.
      destruct cur as [z|] eqn:Ez.
      - (* cur = Some z *)
        simpl in H.
        destruct (betterB x z) eqn:E.
        + inversion H; subst. left; reflexivity.
        + inversion H; subst. right; exists z; split; [reflexivity | reflexivity].
      - (* cur = None *)
        simpl in H. inversion H; subst. left; reflexivity.
    Qed.


    Lemma best_feasible_bid_sound :
      forall Bs Ss b,
        best_feasible_bid Bs Ss = Some b ->
        In b Bs /\
        (exists a, In a Ss /\ matchable b a) /\
        (forall b', In b' Bs ->
          (exists a', In a' Ss /\ matchable b' a') ->
          b' = b \/ PriorityB b b').
    Proof.
      intros Bs Ss.
      induction Bs as [|x t IH]; cbn; intros b H; try discriminate.
      remember (best_feasible_bid t Ss) as r eqn:Er.
      destruct (has_feasible_ask x Ss) eqn:Hhas.
      - (* Case: x has feasible ask *)
        destruct (best_byB r x) eqn:Hbest; inversion H; subst.
        destruct (best_byB_spec _ _ _ Hbest) as [Heq | [z [Hcur Hz]]].
        + (* Subcase: winner is x *)
          subst.
          pose proof (has_feasible_ask_sound _ _ Hhas) as [a [Hin Hm]].
          split; [left; reflexivity|].
          split; [eauto|].
          intros b' Hb' Hex'.
          destruct Hb' as [->|HinT]; [left; reflexivity|].
          destruct r as [rb|] eqn:Erb.
          * rewrite Erb in Hbest.
            destruct (betterB x rb) eqn:Eb; try discriminate.
            apply betterB_correct in Eb as Pxrb.
            destruct (IH _ Erb) as [_ [_ MaxR]].
            destruct (MaxR b' HinT Hex') as [->|Hrbb'].
            -- left; reflexivity.
            -- right. destruct PriorityB_strict_total as [_ [Ptrans _]].
              eapply Ptrans; eauto.
          * (* r = None, contradiction with feasible b' *)
            inversion Hex' as [a' [HinA _]].
            inversion HinT.
        + (* Subcase: winner is from r *)
          subst y.
          specialize (IH _ Hcur) as [Hin [Hex MaxR]].
          split; [right; exact Hin|].
          split; [exact Hex|].
          intros b' Hb' Hex'.
          destruct Hb' as [Hb'|HinT].
          * rewrite Hcur in Hbest.
            destruct (betterB x z) eqn:Eb; try discriminate.
            destruct (Nat.eq_dec y x) as [->|Hneq].
            -- left; reflexivity.
            -- destruct PriorityB_strict_total as [_ [_ Tot]].
              destruct (Tot y x Hneq) as [Hyx | Hxy].
              ++ right; exact Hyx.
              ++ exfalso.
                  apply (proj2 (betterB_correct _ _)) in Hxy.
                  rewrite Hxy in Eb. discriminate.
          * apply MaxR; exact HinT; exact Hex'.
      - (* Case: x has no feasible ask, drop to tail *)
        destruct (best_feasible_bid t Ss) as [rb|] eqn:Erb; rewrite Erb in H; cbn in H.
        + inversion H; subst.
          specialize (IH _ Erb) as [Hin [Hex MaxR]].
          split; [right; exact Hin|].
          split; [exact Hex|].
          intros b' Hb' Hex'.
          destruct Hb' as [Hb'|HinT].
          * (* contradiction: Hhas = false but x is feasible *)
            inversion Hex' as [a' [HinA Hm']].
            clear - Hhas HinA Hm'.
            revert HinA Hm' Hhas.
            induction Ss as [|a0 ts IHs]; cbn; intros; [inversion HinA|].
            destruct HinA as [->|Hin'].
            -- rewrite (proj2 (feasibleb_correct _ _)) in Hhas; congruence.
            -- destruct (feasibleb x a0); auto.
          * apply MaxR; auto.
        + discriminate.
    Qed.

End Matching.

Export Matching.
