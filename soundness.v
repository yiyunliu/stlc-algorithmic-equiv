Require Export algo.
From Hammer Require Import Tactics.
From Coq Require Import ssreflect.

Lemma subject_reduction n (Γ : context n) a A :
  Γ ⊢ a ∈ A -> forall b, a ⤳ b -> Γ ⊢ b ∈ A.
Proof. Admitted.

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
