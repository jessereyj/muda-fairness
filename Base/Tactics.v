(**************************************************************************)
(* Tactics.v - Proof automation for MUDA verification                    *)
(* Coq 8.18.0 compatible                                                  *)
(* NO ADMITS - Complete                                                   *)
(**************************************************************************)

From Coq Require Import Arith Lia List.
From MudaFairness.Base Require Import Prelude.

(** * Basic automation tactics *)

(** Invert and substitute in one step *)
Ltac inv H := inversion H; subst; clear H.

(** Invert and substitute, keeping original hypothesis *)
Ltac invs H := inversion H; subst.

(** Destruct with intro pattern shorthand *)
Ltac destr H := destruct H.
Ltac destr_all := repeat match goal with H : _ |- _ => destruct H end.

(** * Simplification tactics *)

(** Simplify In predicates *)
Ltac simpl_In :=
  repeat match goal with
  | H : In _ [] |- _ => 
      inversion H
  | H : In _ (_ :: _) |- _ => 
      destruct H as [H | H]; [try subst |]
  | |- In _ (_ :: _) => 
      (left; reflexivity) || right
  | H : In _ (_ ++ _) |- _ =>
      apply In_app_iff in H; destruct H
  | |- In _ (_ ++ _) =>
      apply In_app_iff; (left || right)
  end.

(** Simplify list operations *)
Ltac simpl_list :=
  repeat (
    autorewrite with list_simpl in * ||
    match goal with
    | H : _ ++ _ = [] |- _ => apply app_eq_nil in H; destruct H; subst
    | H : [] = _ ++ _ |- _ => symmetry in H; apply app_eq_nil in H; destruct H; subst
    | H : _ :: _ = _ :: _ |- _ => inv H
    | H : length ?l = 0 |- _ => apply length_zero_iff_nil in H; subst
    | H : length (_ :: _) = _ |- _ => simpl in H
    | H : length (_ ++ _) = _ |- _ => rewrite length_app in H
    end
  ).

(** Destruct all pairs and products *)
Ltac destruct_pairs :=
  repeat match goal with
  | H : (_ * _)%type |- _ => destruct H
  | H : (_ * _ * _)%type |- _ => destruct H as [[? ?] ?]
  | H : (_ * _ * _ * _)%type |- _ => destruct H as [[[? ?] ?] ?]
  end.

(** Destruct all exists in hypotheses *)
Ltac destruct_exists :=
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  end.

(** Destruct all conjunctions *)
Ltac destruct_conjs :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

(** Split all conjunctions in goal *)
Ltac split_conjs :=
  repeat match goal with
  | |- _ /\ _ => split
  end.

(** * Decision procedure tactics *)

(** Case analysis on decidable equality *)
Ltac destruct_eqb :=
  repeat match goal with
  | |- context[?x =? ?y] => destruct (Nat.eq_dec x y); subst
  | H : context[?x =? ?y] |- _ => destruct (Nat.eq_dec x y); subst
  | |- context[Nat.eqb ?x ?y] => destruct (Nat.eq_dec x y); subst
  | H : context[Nat.eqb ?x ?y] |- _ => destruct (Nat.eq_dec x y); subst
  end.

(** Case analysis on boolean comparisons *)
Ltac destruct_leb :=
  repeat match goal with
  | |- context[?x <=? ?y] => destruct (le_dec x y)
  | H : context[?x <=? ?y] |- _ => destruct (le_dec x y)
  | |- context[Nat.leb ?x ?y] => destruct (le_dec x y)
  | H : context[Nat.leb ?x ?y] |- _ => destruct (le_dec x y)
  end.

Ltac destruct_ltb :=
  repeat match goal with
  | |- context[?x <? ?y] => destruct (lt_dec x y)
  | H : context[?x <? ?y] |- _ => destruct (lt_dec x y)
  | |- context[Nat.ltb ?x ?y] => destruct (lt_dec x y)
  | H : context[Nat.ltb ?x ?y] |- _ => destruct (lt_dec x y)
  end.

(** Combine all decidable destructs *)
Ltac destruct_decs := 
  destruct_eqb; destruct_leb; destruct_ltb.

(** * Forward reasoning *)

(** Apply hypothesis and introduce result *)
Ltac fwd :=
  match goal with
  | H : ?P -> ?Q, H' : ?P |- _ => 
      let Hnew := fresh "H" in 
      assert (Hnew : Q) by (apply H; exact H')
  end.

(** Repeatedly forward reason *)
Ltac fwd_all := repeat fwd.

(** * Contradiction tactics *)

(** Solve by finding contradictory hypotheses *)
Ltac solve_false :=
  exfalso; 
  match goal with
  | H1 : ?P, H2 : ~ ?P |- _ => 
      apply H2; exact H1
  | H : ?x <> ?x |- _ => 
      apply H; reflexivity
  | H : ?x < ?x |- _ =>
      apply Nat.lt_irrefl in H; contradiction
  | H1 : ?x < ?y, H2 : ?y < ?x |- _ =>
      assert (Hlt : x < x) by (eapply Nat.lt_trans; eauto); 
      apply Nat.lt_irrefl in Hlt; contradiction
  | H1 : ?x < ?y, H2 : ?y <= ?x |- _ =>
      lia
  | H : _ |- _ => 
      congruence || lia || contradiction
  end.

(** Try to solve by contradiction *)
Ltac try_solve_false := try solve_false.

(** * Arithmetic tactics *)

(** Enhanced lia with preprocessing *)
Ltac lia_solve :=
  try solve_false;
  simpl in *;
  try lia.

(** Omega-style tactic (for compatibility) *)
Ltac omega_solve := lia_solve.

(** * Case analysis tactics *)

(** Destruct match expressions in goal *)
Ltac destruct_match :=
  match goal with
  | |- context[match ?x with _ => _ end] => destruct x eqn:?
  | H : context[match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.

(** Destruct if-then-else *)
Ltac destruct_if :=
  match goal with
  | |- context[if ?b then _ else _] => destruct b eqn:?
  | H : context[if ?b then _ else _] |- _ => destruct b eqn:?
  end.

(** Destruct option types *)
Ltac destruct_option :=
  match goal with
  | H : context[match ?o with Some _ => _ | None => _ end] |- _ =>
      destruct o eqn:?
  | |- context[match ?o with Some _ => _ | None => _ end] =>
      destruct o eqn:?
  end.

(** * Induction tactics *)

(** List induction with proper naming *)
Ltac list_induction l :=
  induction l as [| ?x ?xs ?IH]; simpl in *.

(** Natural number induction *)
Ltac nat_induction n :=
  induction n as [| ?n' ?IH]; simpl in *.

(** Strong induction on nat *)
Ltac strong_induction n :=
  induction n as [n IH] using lt_wf_ind.

(** * Proof search tactics *)

(** Basic auto with additional lemmas *)
Ltac auto_muda := 
  auto with core arith list.

(** Enhanced eauto *)
Ltac eauto_muda := 
  eauto 10 with core arith list.

(** Crush simple goals *)
Ltac crush :=
  simpl in *;
  intros;
  destruct_conjs;
  destruct_exists;
  destruct_pairs;
  subst;
  simpl_list;
  try solve [auto_muda | lia_solve | congruence].

(** * Hypothesis management *)

(** Clear trivial hypotheses *)
Ltac clear_trivial :=
  repeat match goal with
  | H : True |- _ => clear H
  | H : ?x = ?x |- _ => clear H
  end.

(** Rename hypothesis *)
Tactic Notation "rename_hyp" hyp(H) "to" ident(name) :=
  rename H into name.

(** * Custom rewrite tactics *)

(** Rewrite and simplify *)
Ltac rw_simpl lem :=
  rewrite lem; simpl.

(** Rewrite everywhere (renamed to avoid notation conflict) *)
Ltac rewrite_everywhere lem :=
  progress repeat (
    try rewrite lem; 
    repeat match goal with H : _ |- _ => try rewrite lem in H end
  ).

(** * Specialized MUDA tactics *)

(** Unfold MUDA-specific definitions *)
Ltac unfold_muda :=
  unfold price, qty, timestamp, agent_id in *.

(** Solve goals about In by exhaustive case analysis *)
Ltac solve_In :=
  simpl_In;
  try solve [auto | congruence | lia].

(** Solve goals about list length *)
Ltac solve_length :=
  simpl_list;
  try solve [simpl; lia | reflexivity].

(** * Debugging tactics *)

(** Show current hypotheses *)
Ltac show_hyps :=
  match goal with
  | |- _ => idtac "Current hypotheses:"; repeat match goal with H : _ |- _ => idtac H ":" H end
  end.

(** Show current goal *)
Ltac show_goal :=
  match goal with
  | |- ?G => idtac "Current goal:"; idtac G
  end.

(** * Ltac combinators *)

(** Try tactic, otherwise do nothing *)
Tactic Notation "try'" tactic3(t) := try t.

(** Repeat tactic until it fails *)
Tactic Notation "repeat'" tactic3(t) := repeat t.

(** First successful tactic *)
Tactic Notation "first" "[" tactic3(t1) "|" tactic3(t2) "]" :=
  first [t1 | t2].

Tactic Notation "first" "[" tactic3(t1) "|" tactic3(t2) "|" tactic3(t3) "]" :=
  first [t1 | t2 | t3].

(** * Hint databases *)

(** Create MUDA-specific hint database *)
Create HintDb muda_db discriminated.

(** Hints for list operations *)
#[export] Hint Resolve in_eq in_cons : muda_db.
#[export] Hint Resolve app_nil_l app_nil_r : muda_db.
#[export] Hint Rewrite @app_nil_l @app_nil_r @app_assoc : muda_db.

(** Hints for arithmetic *)
#[export] Hint Resolve Nat.le_refl Nat.lt_irrefl : muda_db.
#[export] Hint Resolve Nat.le_trans Nat.lt_trans : muda_db.
#[export] Hint Resolve Nat.add_0_r Nat.mul_1_r : muda_db.

(** * Proof cleanup *)

(** Standard cleanup at start of proof *)
Ltac proof_start :=
  intros;
  clear_trivial;
  destruct_conjs;
  destruct_pairs;
  subst.

(** Standard cleanup at end of proof *)
Ltac proof_end :=
  auto_muda || lia_solve || congruence.