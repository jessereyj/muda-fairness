From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore Sorting Tactics.

Module Matching.
  (* Selectors for highest/lowest feasible (Def. 3.1.9). *)
  Parameter HighestFeasibleB : list Bid -> list Ask -> option Bid.
  Parameter LowestFeasibleS  : list Bid -> list Ask -> option Ask.

  (* Soundness of selectors w.r.t. feasibility and priority fairness. *)
  Axiom HighestFeasibleB_sound:
    forall Bs Ss b,
      HighestFeasibleB Bs Ss = Some b ->
      exists a, In b Bs /\ In a Ss /\ matchable b a /\
        (forall b', In b' Bs -> (exists a', In a' Ss /\ matchable b' a') ->
           b' = b \/ PriorityB b b').

  Axiom LowestFeasibleS_sound:
    forall Bs Ss a,
      LowestFeasibleS Bs Ss = Some a ->
      exists b, In a Ss /\ In b Bs /\ matchable b a /\
        (forall a', In a' Ss -> (exists b', In b' Bs /\ matchable b' a') ->
           a' = a \/ PriorityS a a').

  (* One greedy step: we keep the list updates abstract but append the executed match. *)
  Inductive Step : State -> State -> Prop :=
  | step_match :
      forall Bs Ss M b a
        (HB : HighestFeasibleB Bs Ss = Some b)
        (HA : LowestFeasibleS  Bs Ss = Some a)
        (Hfeas : matchable b a),
      let q := q_ij b a in
      q > 0 ->
      forall Bs' Ss',
        q <= q_b b /\ q <= q_s a ->
        Step
          {| Bids := Bs; Asks := Ss; Mt := M |}
          {| Bids := Bs'; Asks := Ss'; Mt := M ++ [{| mb:=b; ma:=a; mq:=q |}] |}.


  (* Invariants over any Step *)
  Lemma step_monotone :
    forall s1 s2, Step s1 s2 -> monotone_Mt (Mt s1) (Mt s2).
  Proof.
    intros [Bs Ss M] [Bs' Ss' M'] H; inversion H; subst; simpl; unfold monotone_Mt; intros m Hin.
    apply in_or_app; now left.
  Qed.

  (* Simpler “member + feasible” witness for the newly appended match. *)
  Lemma step_adds_feasible :
    forall s1 s2, Step s1 s2 ->
    exists m, In m (Mt s2) /\ feasible_match m.
  Proof.
    intros [Bs Ss M] [Bs' Ss' M'] H; inversion H; subst; simpl.
    eexists; split.
    - apply in_or_app; right; simpl; auto.
    - unfold feasible_match; simpl. split; [exact Hfeas | reflexivity].
  Qed.


  (* Multi-step closure *)
  Inductive Steps : State -> State -> Prop :=
  | steps_refl : forall s, Steps s s
  | steps_cons : forall s1 s2 s3, Step s1 s2 -> Steps s2 s3 -> Steps s1 s3.

  Lemma steps_monotone :
    forall s1 s2, Steps s1 s2 -> monotone_Mt (Mt s1) (Mt s2).
  Proof.
    intros s1 s2 H; induction H.
    - (* steps_refl *) intros m Hin; exact Hin.
    - (* steps_cons *) intros m Hin.
      (* Step s1 s2 gives Mt s1 ⊆ Mt s2 *)
      specialize (step_monotone _ _ H) as Mono12.
      (* IH gives Mt s2 ⊆ Mt s3 *)
      specialize (IHSteps) as Mono23.
      (* compose: Mt s1 ⊆ Mt s3 *)
      apply Mono23, Mono12; exact Hin.
  Qed.


  (* Terminality and its property kept abstract, per your plan. *)
  Parameter Terminal : State -> Prop.
  Axiom termination_exists : forall s0, exists sT, Steps s0 sT /\ Terminal sT.

  Parameter no_feasible_pairs_at_terminal :
    forall sT, Terminal sT ->
      forall b a, In b (Bids sT) -> In a (Asks sT) -> ~ matchable b a.
End Matching.

Export Matching.