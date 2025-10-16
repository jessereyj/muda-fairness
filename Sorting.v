From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import MudaCore.

Module Sorting.

  (* Full lexicographic priorities *)
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

  (* Irreflexivity *)
  Lemma PriorityB_irrefl : forall x, ~ PriorityB x x.
  Proof.
    intros [ba px qx tx] H.
    unfold PriorityB in H; simpl in H.
    destruct H as [H | [_ H]]; [lia |].
    destruct H as [H | [_ H]]; [lia |].
    destruct H as [H | [_ H]]; lia.
  Qed.

  Lemma PriorityS_irrefl : forall x, ~ PriorityS x x.
  Proof.
    intros [sa ax qx tx] H.
    unfold PriorityS in H; simpl in H.
    destruct H as [H | [_ H]]; [lia |].
    destruct H as [H | [_ H]]; [lia |].
    destruct H as [H | [_ H]]; lia.
  Qed.

  (* Transitivity *)
  Lemma PriorityB_trans :
    forall x y z, PriorityB x y -> PriorityB y z -> PriorityB x z.
  Proof.
    intros [bax px qx tx] [bay py qy ty] [baz pz qz tz] Hxy Hyz.
    unfold PriorityB in *; simpl in *.
    destruct Hxy as [Hxy|[Eqxy Hxy]];
    destruct Hyz as [Hyz|[Eqyz Hyz]];
    try (left; lia).
    right; split; [lia|].
    destruct Hxy as [Hxy|[Eqtxy Hxy]];
    destruct Hyz as [Hyz|[Eqtyz Hyz]];
    try (left; lia).
    right; split; [lia|].
    destruct Hxy as [Hxy|[Eqaxy Hxy]];
    destruct Hyz as [Hyz|[Eqayz Hyz]];
    try (left; lia).
    right; split; [lia|lia].
  Qed.

  Lemma PriorityS_trans :
    forall x y z, PriorityS x y -> PriorityS y z -> PriorityS x z.
  Proof.
    intros [sax ax qx tx] [say ay qy ty] [saz az qz tz] Hxy Hyz.
    unfold PriorityS in *; simpl in *.
    destruct Hxy as [Hxy|[Eqxy Hxy]];
    destruct Hyz as [Hyz|[Eqyz Hyz]];
    try (left; lia).
    right; split; [lia|].
    destruct Hxy as [Hxy|[Eqtxy Hxy]];
    destruct Hyz as [Hyz|[Eqtyz Hyz]];
    try (left; lia).
    right; split; [lia|].
    destruct Hxy as [Hxy|[Eqaxy Hxy]];
    destruct Hyz as [Hyz|[Eqayz Hyz]];
    try (left; lia).
    right; split; [lia|lia].
  Qed.

  (* Totality - KEY FIX: unfold BEFORE using left/right *)
  Lemma PriorityB_total :
    forall x y, x <> y -> PriorityB x y \/ PriorityB y x.
  Proof.
    intros [ba px qx tx] [bb py qy ty] Hneq.
    unfold PriorityB; simpl.
    destruct (lt_eq_lt_dec px py) as [[Hlt|Heq]|Hgt].
    - (* px < py, so y has priority over x *)
      right. left. lia.
    - (* px = py, check timestamps *)
      subst py.
      destruct (lt_eq_lt_dec tx ty) as [[Hlt|Heq]|Hgt].
      + (* tx < ty, x has priority *)
        left. right. split; [reflexivity|left; lia].
      + (* tx = ty, check agents *)
        subst ty.
        destruct (lt_eq_lt_dec ba bb) as [[Hlt|Heq]|Hgt].
        * (* ba < bb, x has priority *)
          left. right. split; [reflexivity|].
          right. split; [reflexivity|left; lia].
        * (* ba = bb, check quantities *)
          subst bb.
          destruct (lt_eq_lt_dec qx qy) as [[Hlt|Heq]|Hgt].
          -- (* qx < qy, x has priority *)
             left. right. split; [reflexivity|].
             right. split; [reflexivity|].
             right. split; [reflexivity|lia].
          -- (* qx = qy, contradiction *)
             subst qy. exfalso. apply Hneq. reflexivity.
          -- (* qx > qy, y has priority *)
             right. right. split; [reflexivity|].
             right. split; [reflexivity|].
             right. split; [reflexivity|lia].
        * (* ba > bb, y has priority *)
          right. right. split; [reflexivity|].
          right. split; [reflexivity|left; lia].
      + (* tx > ty, y has priority *)
        right. right. split; [reflexivity|left; lia].
    - (* px > py, x has priority *)
      left. left. lia.
  Qed.

  Lemma PriorityS_total :
    forall x y, x <> y -> PriorityS x y \/ PriorityS y x.
  Proof.
    intros [sa ax qx tx] [sb ay qy ty] Hneq.
    unfold PriorityS; simpl.
    destruct (lt_eq_lt_dec ax ay) as [[Hlt|Heq]|Hgt].
    - (* ax < ay, x has priority *)
      left. left. lia.
    - (* ax = ay, check timestamps *)
      subst ay.
      destruct (lt_eq_lt_dec tx ty) as [[Hlt|Heq]|Hgt].
      + (* tx < ty, x has priority *)
        left. right. split; [reflexivity|left; lia].
      + (* tx = ty, check agents *)
        subst ty.
        destruct (lt_eq_lt_dec sa sb) as [[Hlt|Heq]|Hgt].
        * (* sa < sb, x has priority *)
          left. right. split; [reflexivity|].
          right. split; [reflexivity|left; lia].
        * (* sa = sb, check quantities *)
          subst sb.
          destruct (lt_eq_lt_dec qx qy) as [[Hlt|Heq]|Hgt].
          -- (* qx < qy, x has priority *)
             left. right. split; [reflexivity|].
             right. split; [reflexivity|].
             right. split; [reflexivity|lia].
          -- (* qx = qy, contradiction *)
             subst qy. exfalso. apply Hneq. reflexivity.
          -- (* qx > qy, y has priority *)
             right. right. split; [reflexivity|].
             right. split; [reflexivity|].
             right. split; [reflexivity|lia].
        * (* sa > sb, y has priority *)
          right. right. split; [reflexivity|].
          right. split; [reflexivity|left; lia].
      + (* tx > ty, y has priority *)
        right. right. split; [reflexivity|left; lia].
    - (* ax > ay, y has priority *)
      right. left. lia.
  Qed.

  (* Package the three laws *)
  Theorem PriorityB_strict_total :
    (forall x, ~ PriorityB x x) /\
    (forall x y z, PriorityB x y -> PriorityB y z -> PriorityB x z) /\
    (forall x y, x <> y -> PriorityB x y \/ PriorityB y x).
  Proof.
    repeat split.
    - apply PriorityB_irrefl.
    - apply PriorityB_trans.
    - apply PriorityB_total.
  Qed.

  Theorem PriorityS_strict_total :
    (forall x, ~ PriorityS x x) /\
    (forall x y z, PriorityS x y -> PriorityS y z -> PriorityS x z) /\
    (forall x y, x <> y -> PriorityS x y \/ PriorityS y x).
  Proof.
    repeat split.
    - apply PriorityS_irrefl.
    - apply PriorityS_trans.
    - apply PriorityS_total.
  Qed.

End Sorting.

Export Sorting.