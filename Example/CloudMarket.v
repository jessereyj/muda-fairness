(* Example/CloudMarket.v *)
From MUDA Require Import Eqb Types State Sorting Matching ClearingPrice Transitions Atoms.
From LTL Require Import Syntax Semantics Axioms Soundness Completeness LTL.
From Stdlib Require Import List.
Import ListNotations.
From Fairness Require Import All.

Local Open Scope LTL_scope.

Set Implicit Arguments.
Generalizable All Variables.

Definition mk_buyer (id: nat) : Agent := {| agent_id := id; agent_type := Buyer |}.
Definition mk_seller (id: nat) : Agent := {| agent_id := id; agent_type := Seller |}.

Definition B (id p q t: nat) : Bid :=
  {| bid_id := id; buyer := mk_buyer id; price := p; quantity := q; ts := t |}.

Definition A (id p q t: nat) : Ask :=
  {| ask_id := id; seller := mk_seller id; ask_price := p; ask_quantity := q; ask_ts := t |}.


Section Cloud_CaseStudy.
  (* Chapter 5.1 Case Study: Cloud Resource Allocation.

     We scale prices by 100 to stay in nat:
       0.28 -> 28, 0.20 -> 20, etc.

     Table 5.1 (submitted orders):
       Buyers:
         B1 (28,2,1)  B5 (19,1,1)  B4 (26,1,2)
         B2 (24,1,2)  B3 (22,2,3)  B6 (21,1,4)
       Sellers:
         S3 (18,2,1)  S1 (20,3,1)  S2 (23,2,2)
  *)

  Definition b1_cloud : Bid := B 1 28 2 1.
  Definition b5_cloud : Bid := B 5 19 1 1.
  Definition b4_cloud : Bid := B 4 26 1 2.
  Definition b2_cloud : Bid := B 2 24 1 2.
  Definition b3_cloud : Bid := B 3 22 2 3.
  Definition b6_cloud : Bid := B 6 21 1 4.

  Definition s3_cloud : Ask := A 3 18 2 1.
  Definition s1_cloud : Ask := A 1 20 3 1.
  Definition s2_cloud : Ask := A 2 23 2 2.

  (* Orders as submitted in P1 (Table 5.1 order). *)
  Definition bs_cloud : list Bid :=
    [b1_cloud; b5_cloud; b4_cloud; b2_cloud; b3_cloud; b6_cloud].
  Definition as_cloud : list Ask := [s3_cloud; s1_cloud; s2_cloud].

  Definition s0_cloud : State := initial_state bs_cloud as_cloud.
  Definition run_cloud : trace := mu_trace s0_cloud.

  (* Six fairness properties, shown for the cloud-market execution trace. *)
  Example Cloud_Priority : satisfies run_cloud 0 priorityOK.
  Proof. apply priority_fairness_LTL. Qed.

  Example Cloud_Quantity : satisfies run_cloud 0 quantityOK.
  Proof. apply quantity_fairness_LTL_initial. Qed.

  Example Cloud_UniformPrice : satisfies run_cloud 0 priceOK.
  Proof. apply uniform_price_fairness_LTL_initial. Qed.

  Example Cloud_MatchFinality : satisfies run_cloud 0 finalityOK.
  Proof. apply match_finality_LTL. Qed.

  Example Cloud_Maximality : satisfies run_cloud 0 maximal.
  Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.

  Example Cloud_JustifiedRejection : satisfies run_cloud 0 rejectionOK.
  Proof. apply justified_rejection_LTL_initial. Qed.

    (* Execution sanity checks (Chapter 5.1 Table 5.2 and p-star).

      Sorting is axiomatized in MUDA/Sorting.v, so we cannot compute the P2 sort result
      directly. To reflect the Chapter 5 narrative, we explicitly build the state "after
      sorting" by listing bids/asks in the priority order stated in the thesis.

      Buyer priority:  B1 > B4 > B2 > B3 > B6 > B5
      Seller priority: S3 > S1 > S2

      From this post-sorting P3 state, the greedy matching steps are executable, so we can
      compute the four rounds from Table 5.2 and the clearing price p* = 0.20 -> 20.
    *)

  Definition bs_cloud_sorted : list Bid :=
    [b1_cloud; b4_cloud; b2_cloud; b3_cloud; b6_cloud; b5_cloud].
  Definition as_cloud_sorted : list Ask := [s3_cloud; s1_cloud; s2_cloud].

  Definition s_cloud_sorted : State :=
    {| bids := bs_cloud_sorted;
       asks := as_cloud_sorted;
       matches := [];
       clearing_price := None;
       phase := P3 |}.

  Definition m1_cloud : Match := create_match b1_cloud s3_cloud [].
  Definition m2_cloud : Match := create_match b4_cloud s1_cloud [m1_cloud].
  Definition m3_cloud : Match := create_match b2_cloud s1_cloud [m1_cloud; m2_cloud].
  Definition m4_cloud : Match := create_match b3_cloud s1_cloud [m1_cloud; m2_cloud; m3_cloud].

  Example Cloud_Matches_After_Round1 :
    matches (execute 1 s_cloud_sorted) = [m1_cloud].
  Proof. cbv. reflexivity. Qed.

  Example Cloud_Matches_After_Round2 :
    matches (execute 2 s_cloud_sorted) = [m1_cloud; m2_cloud].
  Proof. cbv. reflexivity. Qed.

  Example Cloud_Matches_After_Round3 :
    matches (execute 3 s_cloud_sorted) = [m1_cloud; m2_cloud; m3_cloud].
  Proof. cbv. reflexivity. Qed.

  Example Cloud_Matches_After_Round4 :
    matches (execute 4 s_cloud_sorted) = [m1_cloud; m2_cloud; m3_cloud; m4_cloud].
  Proof. cbv. reflexivity. Qed.

  Example Cloud_P3_Terminates_After_Round4 :
    match_step (execute 4 s_cloud_sorted) = None.
  Proof. cbv. reflexivity. Qed.

  Example Cloud_Enters_P4_After_Termination :
    phase (execute 5 s_cloud_sorted) = P4.
  Proof. cbv. reflexivity. Qed.

  Example Cloud_ClearingPrice_Is_20 :
    clearing_price (execute 6 s_cloud_sorted) = Some 20.
  Proof. cbv. reflexivity. Qed.

  (* Phase P7: rejection is checked against the final match record. *)
  Definition s_cloud_p7 : State := execute 8 s_cloud_sorted.
  Definition mfin_cloud : list Match := [m1_cloud; m2_cloud; m3_cloud; m4_cloud].

  Example Cloud_Phase_Is_P7 : phase s_cloud_p7 = P7.
  Proof. cbv. reflexivity. Qed.

  Example Cloud_Mfin_At_P7 : matches s_cloud_p7 = mfin_cloud.
  Proof. cbv. reflexivity. Qed.

  Example Cloud_Bids_At_P7 : bids s_cloud_p7 = bs_cloud_sorted.
  Proof. cbv. reflexivity. Qed.

  Example Cloud_Rejected_B6 : rejected_bid_prop b6_cloud s_cloud_p7.
  Proof.
    unfold rejected_bid_prop.
    split.
    - rewrite Cloud_Bids_At_P7. simpl. right. right. right. right. left. reflexivity.
    - unfold occurs_bid. intros [m [Hm_in Hm_eq]].
      rewrite Cloud_Mfin_At_P7 in Hm_in.
      simpl in Hm_in.
      destruct Hm_in as [Hm|[Hm|[Hm|[Hm|[]]]]]; subst m;
        cbn in Hm_eq;
        apply (f_equal bid_id) in Hm_eq;
        cbn in Hm_eq;
        discriminate.
  Qed.

  Example Cloud_Rejected_B5 : rejected_bid_prop b5_cloud s_cloud_p7.
  Proof.
    unfold rejected_bid_prop.
    split.
    - rewrite Cloud_Bids_At_P7. simpl. right. right. right. right. right. left. reflexivity.
    - unfold occurs_bid. intros [m [Hm_in Hm_eq]].
      rewrite Cloud_Mfin_At_P7 in Hm_in.
      simpl in Hm_in.
      destruct Hm_in as [Hm|[Hm|[Hm|[Hm|[]]]]]; subst m;
        cbn in Hm_eq;
        apply (f_equal bid_id) in Hm_eq;
        cbn in Hm_eq;
        discriminate.
  Qed.

  Example Cloud_B3_Occurs_In_Mfin : occurs_bid b3_cloud (matches s_cloud_p7).
  Proof.
    unfold occurs_bid.
    exists m4_cloud.
    split.
    - rewrite Cloud_Mfin_At_P7. cbn. right. right. right. left. reflexivity.
    - cbn. reflexivity.
  Qed.

End Cloud_CaseStudy.


Section Case_1.
  (* Chapter 5 Case 1:
     b1=(100,1,1), b2=(90,1,2), b3=(95,1,3); s1=(85,1,1) *)
  Definition bs1 : list Bid := [B 1 100 1 1; B 2 90 1 2; B 3 95 1 3].
  Definition as1 : list Ask := [A 1 85 1 1].
  Definition s0_case_1 : State := initial_state bs1 as1.
  Definition run_case_1 : trace := mu_trace s0_case_1.

  Example Case1_Priority :
    satisfies run_case_1 0 priorityOK.
  Proof. apply priority_fairness_LTL. Qed.

  Example Case1_Quantity :
    satisfies run_case_1 0 quantityOK.
  Proof. apply quantity_fairness_LTL_initial. Qed.

  Example Case1_UniformPrice :
    satisfies run_case_1 0 priceOK.
  Proof. apply uniform_price_fairness_LTL_initial. Qed.

  Example Case1_MatchFinality :
    satisfies run_case_1 0 finalityOK.
  Proof. apply match_finality_LTL. Qed.

  Example Case1_Maximality :
    satisfies run_case_1 0 maximal.
  Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.

End Case_1.

Section Case_2.
  (* Chapter 5 Case 2:
     b1=(80,1,1); s1=(85,1,1), s2=(90,1,2) *)
  Definition bs2 : list Bid := [B 1 80 1 1].
  Definition as2 : list Ask := [A 1 85 1 1; A 2 90 1 2].
  Definition s0_case_2 : State := initial_state bs2 as2.
  Definition run_case_2 : trace := mu_trace s0_case_2.

  Example Case2_Priority : satisfies run_case_2 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case2_Quantity : satisfies run_case_2 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case2_UniformPrice : satisfies run_case_2 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case2_MatchFinality :  satisfies run_case_2 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case2_Maximality: satisfies run_case_2 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
  Example Case2_Rejection :
    satisfies run_case_2 0 rejectionOK.
  Proof. apply justified_rejection_LTL_initial. Qed.
End Case_2.

Section Case_3.
  (* Chapter 5 Case 3:
     b1=(100,2,1), b2=(95,2,2); s1=(80,2,1), s2=(85,2,2) *)
  Definition bs3 : list Bid := [B 1 100 2 1; B 2 95 2 2].
  Definition as3 : list Ask := [A 1 80 2 1; A 2 85 2 2].
  Definition s0_case_3 : State := initial_state bs3 as3.
  Definition run_case_3 : trace := mu_trace s0_case_3.

  Example Case3_Priority : satisfies run_case_3 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case3_Quantity : satisfies run_case_3 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case3_UniformPrice : satisfies run_case_3 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case3_MatchFinality :  satisfies run_case_3 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case3_Maximality: satisfies run_case_3 0 maximal.
  Proof. apply maximality_from_P1_or_P2. left. reflexivity. Qed.
End Case_3.

Section Case_4.
  (* Chapter 5 Case 4:
     b1=(100,1,1), b2=(100,1,2); s1=(90,1,1) *)
  Definition bs4 : list Bid := [B 1 100 1 1; B 2 100 1 2].
  Definition as4 : list Ask := [A 1 90 1 1].
  Definition s0_case_4 : State := initial_state bs4 as4.
  Definition run_case_4 : trace := mu_trace s0_case_4.

  Example Case4_Priority : satisfies run_case_4 0 priorityOK.
  Proof. apply priority_fairness_LTL. Qed.
  Example Case4_Quantity : satisfies run_case_4 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case4_UniformPrice : satisfies run_case_4 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case4_MatchFinality :  satisfies run_case_4 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case4_Maximality: satisfies run_case_4 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
End Case_4.

Section Case_5.
  (* Chapter 5 Case 5:
     b1=(100,5,1); s1=(80,2,1) *)
  Definition bs5 : list Bid := [B 1 100 5 1].
  Definition as5 : list Ask := [A 1 80 2 1].
  Definition s0_case_5 : State := initial_state bs5 as5.
  Definition run_case_5 : trace := mu_trace s0_case_5.

  Example Case5_Priority : satisfies run_case_5 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case5_Quantity : satisfies run_case_5 0 quantityOK.
  Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case5_UniformPrice : satisfies run_case_5 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case5_MatchFinality :  satisfies run_case_5 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case5_Maximality: satisfies run_case_5 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
End Case_5.

Section Case_6.
  (* Chapter 5 Case 6:
     b1=(100,3,1), b2=(90,2,2); s1=(80,2,1), s2=(85,2,2) *)
  Definition bs6 : list Bid := [B 1 100 3 1; B 2 90 2 2].
  Definition as6 : list Ask := [A 1 80 2 1; A 2 85 2 2].
  Definition s0_case_6 : State := initial_state bs6 as6.
  Definition run_case_6 : trace := mu_trace s0_case_6.

  Example Case6_Priority : satisfies run_case_6 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case6_Quantity : satisfies run_case_6 0 quantityOK.
  Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case6_UniformPrice : satisfies run_case_6 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case6_MatchFinality :  satisfies run_case_6 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case6_Maximality: satisfies run_case_6 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
End Case_6.

Section Case_7.
  (* Chapter 5 Case 7:
     b1=(110,3,1), b2=(105,2,2), b3=(100,1,3);
     s1=(85,2,1), s2=(90,2,2), s3=(95,1,3) *)
  Definition bs7 : list Bid := [B 1 110 3 1; B 2 105 2 2; B 3 100 1 3].
  Definition as7 : list Ask := [A 1 85 2 1; A 2 90 2 2; A 3 95 1 3].
  Definition s0_case_7 : State := initial_state bs7 as7.
  Definition run_case_7 : trace := mu_trace s0_case_7.

  Example Case7_Priority : satisfies run_case_7 0 priorityOK. Proof. apply priority_fairness_LTL. Qed.
  Example Case7_Quantity : satisfies run_case_7 0 quantityOK.   Proof. apply quantity_fairness_LTL_initial. Qed.
  Example Case7_UniformPrice : satisfies run_case_7 0 priceOK. Proof. apply uniform_price_fairness_LTL_initial. Qed.
  Example Case7_MatchFinality :  satisfies run_case_7 0 finalityOK.     Proof. apply match_finality_LTL. Qed.
  Example Case7_Maximality: satisfies run_case_7 0 maximal.       Proof.
    apply maximality_from_P1_or_P2. left. reflexivity.
  Qed.
  Example Case7_Rejection :
    satisfies run_case_7 0 rejectionOK.
  Proof. apply justified_rejection_LTL_initial. Qed.
End Case_7.

Section Case_8.
  (* Chapter 5 Case 8:
     Degenerate market: buyers exist, but no sellers submit any ask.
     b1=(100,2,1), b2=(90,1,2); S = ∅ *)
  Definition bs8 : list Bid := [B 1 100 2 1; B 2 90 1 2].
  Definition as8 : list Ask := [].
  Definition s0_case_8 : State := initial_state bs8 as8.
  Definition run_case_8 : trace := mu_trace s0_case_8.

  Example Case8_Priority : satisfies run_case_8 0 priorityOK.
  Proof. apply priority_fairness_LTL. Qed.

  Example Case8_Quantity : satisfies run_case_8 0 quantityOK.
  Proof. apply quantity_fairness_LTL_initial. Qed.

  Example Case8_UniformPrice : satisfies run_case_8 0 priceOK.
  Proof. apply uniform_price_fairness_LTL_initial. Qed.

  Example Case8_MatchFinality : satisfies run_case_8 0 finalityOK.
  Proof. apply match_finality_LTL. Qed.

  Example Case8_Maximality : satisfies run_case_8 0 maximal.
  Proof. apply maximality_from_P1_or_P2. left. reflexivity. Qed.

  Example Case8_Rejection : satisfies run_case_8 0 rejectionOK.
  Proof. apply justified_rejection_LTL_initial. Qed.
End Case_8.
