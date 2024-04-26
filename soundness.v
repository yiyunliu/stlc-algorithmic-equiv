Require Export algo.
From Hammer Require Import Tactics.
From Coq Require Import ssreflect.

Definition ren_ok {n m} ξ (Γ : context n) (Δ : context m) :=
  forall i, Γ i = Δ (ξ i).

Lemma renaming n m ξ (Γ : context n) (Δ : context m) a A :
  ren_ok ξ Γ Δ ->
  Γ ⊢ a ∈ A ->
  Δ ⊢ ren_tm ξ a ∈ A.
Proof.
  move => + h. move : m ξ Δ.
  elim : n Γ a A / h; hauto q:on inv:option ctrs:Wt unfold:ren_ok.
Qed.

Definition subst_ok {n m} ρ (Γ : context n) (Δ : context m) :=
  forall i, Δ ⊢ ρ i ∈ Γ i.

Lemma subst_ok_up n m (ρ : fin n -> tm m) Γ Δ A  :
  subst_ok ρ Γ Δ ->
  subst_ok (up_tm_tm ρ) (A .: Γ) (A .: Δ).
Proof.
  rewrite /subst_ok => h.
  destruct i as [i | ] => /=; asimpl.
  - move /renaming : (Δ). by apply.
  - apply T_Var.
Qed.

Lemma morphing n m ρ (Γ : context n) (Δ : context m) a A :
  subst_ok ρ Γ Δ ->
  Γ ⊢ a ∈ A ->
  Δ ⊢ subst_tm ρ a ∈ A.
Proof.
  move => + h. move : m ρ Δ.
  elim : n Γ a A / h; hauto q:on ctrs:Wt use:subst_ok_up unfold:subst_ok.
Qed.

Lemma subst_one n (Γ : context n) b A B (h : A .: Γ ⊢ b ∈ B) a (h0 : Γ ⊢ a ∈ A) :
  Γ ⊢ subst_tm (a..) b ∈ B.
Proof.
  apply : morphing h.
  rewrite /subst_ok.
  destruct i as [i|] => //=.
  apply T_Var.
Qed.

Lemma subject_reduction n (Γ : context n) a A :
  Γ ⊢ a ∈ A -> forall b, a ⤳ b -> Γ ⊢ b ∈ A.
Proof.
  move => + b h. move : Γ A.
  elim : a b / h.
  - hauto lq:on ctrs:Wt inv:Wt.
  - hauto l:on inv:Wt use:subst_one.
Qed.

Lemma subject_reduction_eval : forall n (Γ : context n) a A,
  Γ ⊢ a ∈ A -> forall p, a ⇓ p -> Γ ⊢ p ∈ A.
Proof.
  move => n + a + + p h.
  elim : a p / h; hauto l:on use:subject_reduction unfold:whnf.
Qed.

Lemma soundness : forall n (Γ : context n),
  (forall s t A, Γ ⊢ s ⇔ t ∈ A -> Γ ⊢ s ∈ A -> Γ ⊢ t ∈ A -> Γ ⊢ s ≡ t ∈ A) /\
  (forall p q A, Γ ⊢ p ↔ q ∈ A -> Γ ⊢ p ∈ A -> Γ ⊢ q ∈ A -> Γ ⊢ p ≡ q ∈ A).
Proof.
  apply algo_mutual_ind.
  - move => n Γ s p t q hs ht hpq ihpq hs' ht'.
Admitted.
