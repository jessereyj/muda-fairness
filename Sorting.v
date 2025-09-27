From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore.

Module Sorting.
  (* Concrete lexicographic priorities:
     Buyers: higher price first; ties: earlier time first.
     Sellers: lower ask first;  ties: earlier time first. *)

(* Extend your definitions near the top of Sorting.v *)

  Definition PriorityB (b1 b2 : Bid) : Prop :=
    (p_b b1 > p_b b2) \/
    (p_b b1 = p_b b2 /\
      (t_b b1 < t_b b2 \/
        (t_b b1 = t_b b2 /\
          (b_agent b1 < b_agent b2 \/
            (b_agent b1 = b_agent b2 /\ q_b b1 < q_b b2))))).

  Definition PriorityS (a1 a2 : Ask) : Prop :=
    (a_s a1 < a_s a2) \/
    (a_s a1 = a_s a2 /\
      (t_s a1 < t_s a2 \/
        (t_s a1 = t_s a2 /\
          (s_agent a1 < s_agent a2 \/
            (s_agent a1 = s_agent a2 /\ q_s a1 < q_s a2))))).


  (* Irreflexive *)
  Lemma PriorityB_irrefl : forall x, ~ PriorityB x x.
  Proof. intros x [Hp|[He Ht]]; lia. Qed.

  Lemma PriorityS_irrefl : forall x, ~ PriorityS x x.
  Proof. intros x [Hp|[He Ht]]; lia. Qed.

  (* Transitivity for buyers: (p_b x > p_b y) \/ (p_b x = p_b y /\ t_b x < t_b y) *)
  Lemma PriorityB_trans :
    forall x y z, PriorityB x y -> PriorityB y z -> PriorityB x z.
  Proof.
    intros x y z Hxy Hyz.
    destruct Hxy as [Hxpy|[Heqxy Htxy]];
    destruct Hyz as [Hypz|[Heqyz Htyz]].
    - (* price >, price > *) left; lia.
    - (* price >, equal price & earlier time *) left; lia.  (* p_x > p_y = p_z *)
    - (* equal price & earlier time, price > *)
      left; lia.  (* p_x = p_y > p_z  ⇒ p_x > p_z *)
    - (* equal price chain, time chain *)
      right; split; lia.  (* p_x = p_y = p_z and t_x < t_y < t_z ⇒ t_x < t_z *)
  Qed.

  (* Transitivity for sellers: (a_s x < a_s y) \/ (a_s x = a_s y /\ t_s x < t_s y) *)
  Lemma PriorityS_trans :
    forall x y z, PriorityS x y -> PriorityS y z -> PriorityS x z.
  Proof.
    intros x y z Hxy Hyz.
    destruct Hxy as [Hxay|[Heqxy Htxy]];
    destruct Hyz as [Hyaz|[Heqyz Htyz]].
    - (* ask <, ask < *) left; lia.
    - (* ask <, equal ask & earlier time *) left; lia.  (* a_x < a_y = a_z *)
    - (* equal ask & earlier time, ask < *)
      left; lia.  (* a_x = a_y < a_z  ⇒ a_x < a_z *)
    - (* equal ask chain, time chain *)
      right; split; lia.  (* a_x = a_y = a_z and t_x < t_y < t_z ⇒ t_x < t_z *)
  Qed.

  (* ---------- Strict totality via full lexicographic order ---------- *)
  (* Buyers: (p_b desc, t_b asc, b_agent asc, q_b asc) *)
  Lemma PriorityB_total :
    forall x y, x <> y -> PriorityB x y \/ PriorityB y x.
  Proof.
    intros [ba px qx tx] [bb py qy ty] Hneq; cbn in *.
    (* price first: compare px vs py *)
    destruct (Nat.compare px py) eqn:Cp.
    - (* px = py *)
      apply Nat.compare_eq in Cp; subst py.
      (* time next: compare tx vs ty *)
      destruct (Nat.compare tx ty) eqn:Ct.
      + (* tx = ty *)
        apply Nat.compare_eq in Ct; subst ty.
        (* agent next: compare ba vs bb *)
        destruct (Nat.compare ba bb) eqn:Ca.
        * (* ba = bb *)
          apply Nat.compare_eq in Ca; subst bb.
          (* quantity last: compare qx vs qy *)
          destruct (Nat.compare qx qy) eqn:Cq.
          { (* all fields equal -> contradiction with x <> y *)
            apply Nat.compare_eq in Cq; subst qy. congruence. }
          { (* qx < qy -> PriorityB x y with deepest tie-breaker *)
            apply Nat.compare_lt_iff in Cq.
            left. right. (* price equal branch *)
            split; [reflexivity|].
            right. split; [reflexivity|].
            right. split; [reflexivity|].
            exact Cq.
          }
          { (* qx > qy -> PriorityB y x with deepest tie-breaker *)
            apply Nat.compare_gt_iff in Cq.
            right. right.
            split; [reflexivity|].
            right. split; [reflexivity|].
            right. split; [reflexivity|].
            exact Cq.
          }
        * (* ba < bb -> PriorityB x y (price=time equal; agent tie-breaker) *)
          apply Nat.compare_lt_iff in Ca.
          left. right.
          split; [reflexivity|].
          right. split; [reflexivity|].
          left. exact Ca.
        * (* ba > bb -> PriorityB y x *)
          apply Nat.compare_gt_iff in Ca.
          right. right.
          split; [reflexivity|].
          right. split; [reflexivity|].
          left. exact Ca.
      + (* tx < ty -> PriorityB x y (price equal; earlier time wins) *)
        apply Nat.compare_lt_iff in Ct.
        left. right. split; [reflexivity|left; exact Ct].
      + (* tx > ty -> PriorityB y x *)
        apply Nat.compare_gt_iff in Ct.
        right. right. split; [reflexivity|left; exact Ct].
    - (* px < py -> PriorityB y x (higher price wins) *)
      apply Nat.compare_lt_iff in Cp.
      right. left. exact Cp.
    - (* px > py -> PriorityB x y *)
      apply Nat.compare_gt_iff in Cp.
      left. left. exact Cp.
  Qed.

  (* Sellers: (a_s asc, t_s asc, s_agent asc, q_s asc) *)
  Lemma PriorityS_total :
    forall x y, x <> y -> PriorityS x y \/ PriorityS y x.
  Proof.
    intros [sa ax qx tx] [sb ay qy ty] Hneq; cbn in *.
    (* ask first: compare ax vs ay *)
    destruct (Nat.compare ax ay) eqn:Ca.
    - (* ax = ay *)
      apply Nat.compare_eq in Ca; subst ay.
      (* time next: compare tx vs ty *)
      destruct (Nat.compare tx ty) eqn:Ct.
      + (* tx = ty *)
        apply Nat.compare_eq in Ct; subst ty.
        (* agent next: compare sa vs sb *)
        destruct (Nat.compare sa sb) eqn:Cs.
        * (* sa = sb *)
          apply Nat.compare_eq in Cs; subst sb.
          (* quantity last: compare qx vs qy *)
          destruct (Nat.compare qx qy) eqn:Cq.
          { apply Nat.compare_eq in Cq; subst qy. congruence. }
          { (* qx < qy -> PriorityS x y with deepest tie-breaker *)
            apply Nat.compare_lt_iff in Cq.
            left. right.
            split; [reflexivity|].
            right. split; [reflexivity|].
            right. split; [reflexivity|].
            exact Cq.
          }
          { (* qx > qy -> PriorityS y x *)
            apply Nat.compare_gt_iff in Cq.
            right. right.
            split; [reflexivity|].
            right. split; [reflexivity|].
            right. split; [reflexivity|].
            exact Cq.
          }
        * (* sa < sb -> PriorityS x y *)
          apply Nat.compare_lt_iff in Cs.
          left. right.
          split; [reflexivity|].
          right. split; [reflexivity|].
          left. exact Cs.
        * (* sa > sb -> PriorityS y x *)
          apply Nat.compare_gt_iff in Cs.
          right. right.
          split; [reflexivity|].
          right. split; [reflexivity|].
          left. exact Cs.
      + (* tx < ty -> PriorityS x y *)
        apply Nat.compare_lt_iff in Ct.
        left. right. split; [reflexivity|left; exact Ct].
      + (* tx > ty -> PriorityS y x *)
        apply Nat.compare_gt_iff in Ct.
        right. right. split; [reflexivity|left; exact Ct].
    - (* ax < ay -> PriorityS x y (lower ask wins) *)
      apply Nat.compare_lt_iff in Ca. left. left. exact Ca.
    - (* ax > ay -> PriorityS y x *)
      apply Nat.compare_gt_iff in Ca. right. left. exact Ca.
  Qed.



  (* Pack the three laws as your former “strict_total” tuples *)
  Theorem PriorityB_strict_total :
    (forall x, ~ PriorityB x x) /\
    (forall x y z, PriorityB x y -> PriorityB y z -> PriorityB x z) /\
    (forall x y, x <> y -> PriorityB x y \/ PriorityB y x).
  Proof.
    repeat split; [apply PriorityB_irrefl|apply PriorityB_trans|apply PriorityB_total].
  Qed.

  Theorem PriorityS_strict_total :
    (forall x, ~ PriorityS x x) /\
    (forall x y z, PriorityS x y -> PriorityS y z -> PriorityS x z) /\
    (forall x y, x <> y -> PriorityS x y \/ PriorityS y x).
  Proof.
    repeat split; [apply PriorityS_irrefl|apply PriorityS_trans|apply PriorityS_total].
  Qed.

  (* Backwards-compat “documentation lemmas” now provable, not axioms *)
  Theorem PriorityB_price_time :
    forall b1 b2,
      p_b b1 > p_b b2 \/ (p_b b1 = p_b b2 /\ t_b b1 < t_b b2) ->
      PriorityB b1 b2.
  Proof.
    intros b1 b2 [Hgt | [Heq Ht]].
    - (* higher bid price wins *)
      left; exact Hgt.
    - (* equal price, earlier time wins *)
      right; split; [exact Heq| left; exact Ht].
  Qed.

  Theorem PriorityS_price_time :
    forall a1 a2,
      a_s a1 < a_s a2 \/ (a_s a1 = a_s a2 /\ t_s a1 < t_s a2) ->
      PriorityS a1 a2.
  Proof.
    intros a1 a2 [Hlt | [Heq Ht]].
    - (* lower ask wins *)
      left; exact Hlt.
    - (* equal ask, earlier time wins *)
      right; split; [exact Heq| left; exact Ht].
  Qed.

End Sorting.

Export Sorting.
