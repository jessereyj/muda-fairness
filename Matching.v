From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import MudaCore Sorting Tactics.

Module Matching.

  (* ---------- Residual quantity updates - Definition 3.1.6 step 4 ---------- *)

  Definition update_bid_quantity (b:Bid) (q:nat) : option Bid :=
    let q' := q_b b - q in
    if Nat.leb 1 q' then
      Some {| b_agent := b_agent b; p_b := p_b b; q_b := q'; t_b := t_b b |}
    else None.

  Definition update_ask_quantity (a:Ask) (q:nat) : option Ask :=
    let q' := q_s a - q in
    if Nat.leb 1 q' then
      Some {| s_agent := s_agent a; a_s := a_s a; q_s := q'; t_s := t_s a |}
    else None.

  (* Remove or update order in list *)
  Fixpoint update_bid_list (b:Bid) (b_opt:option Bid) (Bs:list Bid) : list Bid :=
    match Bs with
    | [] => []
    | h::t =>
        if (Nat.eqb (b_agent h) (b_agent b)) && (Nat.eqb (p_b h) (p_b b)) && 
           (Nat.eqb (q_b h) (q_b b)) && (Nat.eqb (t_b h) (t_b b))
        then match b_opt with Some b' => b'::t | None => t end
        else h :: update_bid_list b b_opt t
    end.

  Fixpoint update_ask_list (a:Ask) (a_opt:option Ask) (As:list Ask) : list Ask :=
    match As with
    | [] => []
    | h::t =>
        if (Nat.eqb (s_agent h) (s_agent a)) && (Nat.eqb (a_s h) (a_s a)) && 
           (Nat.eqb (q_s h) (q_s a)) && (Nat.eqb (t_s h) (t_s a))
        then match a_opt with Some a' => a'::t | None => t end
        else h :: update_ask_list a a_opt t
    end.

  (* ---------- Boolean comparators - consistent with Sorting.v ---------- *)

  Definition betterB (x y:Bid) : bool :=
    (p_b y <? p_b x) ||
    ((p_b x =? p_b y) &&
      ((t_b x <? t_b y) ||
        ((t_b x =? t_b y) &&
          ((b_agent x <? b_agent y) ||
            ((b_agent x =? b_agent y) && (q_b x <? q_b y)))))).

  Definition betterS (x y:Ask) : bool :=
    (a_s x <? a_s y) ||
    ((a_s x =? a_s y) &&
      ((t_s x <? t_s y) ||
        ((t_s x =? t_s y) &&
          ((s_agent x <? s_agent y) ||
            ((s_agent x =? s_agent y) && (q_s x <? q_s y)))))).

  Definition feasibleb (b:Bid) (a:Ask) : bool :=
    Nat.leb (a_s a) (p_b b) && Nat.leb 1 (q_b b) && Nat.leb 1 (q_s a).

  (* ---------- Find best feasible pair - Definition 3.1.6 step 2 ---------- *)

  Fixpoint find_best_bid (Bs:list Bid) (As:list Ask) : option Bid :=
    match Bs with
    | [] => None
    | b::rest =>
        if existsb (feasibleb b) As
        then match find_best_bid rest As with
             | None => Some b
             | Some b' => if betterB b b' then Some b else Some b'
             end
        else find_best_bid rest As
    end.

  Fixpoint find_best_ask_for (b:Bid) (As:list Ask) : option Ask :=
    match As with
    | [] => None
    | a::rest =>
        if feasibleb b a
        then match find_best_ask_for b rest with
             | None => Some a
             | Some a' => if betterS a a' then Some a else Some a'
             end
        else find_best_ask_for b rest
    end.

  Definition find_best_pair (Bs:list Bid) (As:list Ask) : option (Bid * Ask) :=
    match find_best_bid Bs As with
    | None => None
    | Some b =>
        match find_best_ask_for b As with
        | None => None
        | Some a => Some (b, a)
        end
    end.

  (* ---------- Single matching step - Definition 3.1.6 steps 2-6 ---------- *)

  Definition match_step (s:State) : State :=
    match find_best_pair (Bids s) (Asks s) with
    | None => s  (* No feasible pair - termination *)
    | Some (b, a) =>
        let q := q_ij b a in
        let new_match := {| mb := b; ma := a; mq := q |} in
        let b' := update_bid_quantity b q in
        let a' := update_ask_quantity a q in
        let exhaustion :=
          match b', a' with
          | None, None => BothExhausted
          | None, Some _ => BuyerExhausted
          | Some _, None => SellerExhausted
          | Some _, Some _ => BothExhausted  (* shouldn't happen with min *)
          end in
        {| Bids := update_bid_list b b' (Bids s);
           Asks := update_ask_list a a' (Asks s);
           Mt := (Mt s) ++ [new_match];
           marginal_pair := Some (b, a, exhaustion);
           step_number := S (step_number s)
        |}
    end.

  (* ---------- Greedy algorithm - Definition 3.1.6 step 7 ---------- *)

  Fixpoint greedy_match (fuel:nat) (s:State) : State :=
    match fuel with
    | 0 => s
    | S n =>
        let s' := match_step s in
        if Nat.eqb (step_number s') (step_number s)
        then s  (* No progress - terminated *)
        else greedy_match n s'
    end.

  (* ---------- Terminal state - no feasible pairs ---------- *)

  Definition is_terminal (s:State) : Prop :=
    forall b a, In b (Bids s) -> In a (Asks s) -> ~ matchable b a.

  (* ---------- Correctness lemmas ---------- *)

  Lemma match_step_monotone :
    forall s, monotone_Mt (Mt s) (Mt (match_step s)).
  Proof.
    intros s. unfold match_step.
    destruct (find_best_pair (Bids s) (Asks s)) as [[b a]|]; simpl.
    - unfold monotone_Mt. intros m Hin.
      apply in_app_iff. left. exact Hin.
    - unfold monotone_Mt. intros m Hin. exact Hin.
  Qed.

  Lemma greedy_match_monotone :
    forall fuel s, monotone_Mt (Mt s) (Mt (greedy_match fuel s)).
  Proof.
    induction fuel; intros s; simpl.
    - unfold monotone_Mt. auto.
    - destruct (Nat.eqb (step_number (match_step s)) (step_number s)) eqn:E.
      + unfold monotone_Mt. auto.
      + unfold monotone_Mt. intros m Hin.
        apply IHfuel. apply match_step_monotone. exact Hin.
  Qed.

End Matching.

Export Matching.