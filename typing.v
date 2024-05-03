Require Export syntax ssrbool ssreflect.
From Hammer Require Import Tactics.

Definition context n := fin n -> ty.

Reserved Notation "Γ ⊢ a ∈ A" (at level 70).
Inductive Wt {n} (Γ : context n) : tm n -> ty -> Prop :=
| T_Var i :
  (* ----------- *)
  Γ ⊢ var_tm i ∈ Γ i

| T_Abs A b B :
  A.:Γ ⊢ b ∈ B ->
  (* ------------ *)
  Γ ⊢ Lam A b ∈ Fun A B

| T_App A B b a :
  Γ ⊢ b ∈ Fun A B ->
  Γ ⊢ a ∈ A ->
  (* -------------- *)
  Γ ⊢ App b a ∈ B

| T_Unit :
  (* ------------- *)
  Γ ⊢ TmUnit ∈ TyUnit
where "Γ ⊢ a ∈ A" := (Wt Γ a A).

Reserved Notation "Γ ⊢ a ≡ b ∈ A" (at level 70).
Inductive DEquiv {n} (Γ : context n) : tm n -> tm n -> ty -> Prop :=
| DE_Refl a A :
  Γ ⊢ a ∈ A ->
  (* ----------- *)
  Γ ⊢ a ≡ a ∈ A
| DE_Sym a b A :
  Γ ⊢ a ≡ b ∈ A ->
  (* ---------- *)
  Γ ⊢ b ≡ a ∈ A
| DE_Trans a b c A :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ b ≡ c ∈ A ->
  (* ------------ *)
  Γ ⊢ a ≡ c ∈ A
| DE_Abs b0 b1 A B :
  A.:Γ ⊢ b0 ≡ b1 ∈ B ->
  (* -------------  *)
  Γ ⊢ Lam A b0 ≡ Lam A b1 ∈ Fun A B
| DE_App b0 b1 a0 a1 A B :
  Γ ⊢ b0 ≡ b1 ∈ Fun A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  (*--------------------  *)
  Γ ⊢ App b0 a0 ≡ App b1 a1 ∈ B
| DE_AppAbs b0 b1 a0 a1 A B :
  A.:Γ ⊢ b0 ≡ b1 ∈ B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  (* ---------------- *)
  Γ ⊢ App (Lam A b0) a0 ≡ subst_tm (a1..) b1 ∈ B
| DE_Unit a b :
  Γ ⊢ a ∈ TyUnit ->
  Γ ⊢ b ∈ TyUnit ->
  (* --------------- *)
  Γ ⊢ a ≡ b ∈ TyUnit
where "Γ ⊢ a ≡ b ∈ A" := (DEquiv Γ a b A).

Definition whnf {n} (a : tm n) :=
  match a with
  | TmUnit => true
  | Lam _ _ => true
  | _ => false
  end.

Reserved Notation "Γ ⊢ a ⤳ b ∈ A" (at level 70).
Inductive Red {n} (Γ : context n) : tm n -> tm n -> ty -> Prop :=
(* R_App and R_AppAbs don't overlap because Abs can't be reduced *)
| R_App b0 b1 a A B :
  Γ ⊢ b0 ⤳ b1 ∈ Fun A B ->
  Γ ⊢ a ∈ A ->
  (* ---------------- *)
  Γ ⊢ App b0 a ⤳ App b1 a ∈ B
| R_AppAbs b a A B :
  A.:Γ ⊢ b ∈ B ->
  Γ ⊢ a ∈ A ->
  (* ---------------- *)
  Γ ⊢ App (Lam A b) a ⤳ subst_tm (a..) b ∈ B
where "Γ ⊢ a ⤳ b ∈ A" := (Red Γ a b A).

Reserved Notation "Γ ⊢ a ⤳* b ∈ A" (at level 70, no associativity).
Inductive Reds {n} (Γ : context n) (a : tm n) : tm n -> ty -> Prop :=
| Rs_Refl A :
  Γ ⊢ a ∈ A ->
  Γ ⊢ a ⤳* a ∈ A
| Rs_Step b c A :
  Γ ⊢ a ⤳ b ∈ A ->
  Γ ⊢ b ∈ A ->
  Γ ⊢ b ⤳* c ∈ A ->
  Γ ⊢ a ⤳* c ∈ A
where "Γ ⊢ a ⤳* b ∈ A" := (Reds Γ a b A).

Definition ren_ok {n m} ξ (Γ : context n) (Δ : context m) :=
  forall i, Γ i = Δ (ξ i).

Fixpoint LR {n} (Γ : context n) (b0 b1 : tm n) (A : ty) : Prop :=
  match A with
  | TyUnit => Γ ⊢ b0 ∈ TyUnit /\ Γ ⊢ b1 ∈ TyUnit
  | Fun A B => Γ ⊢ b0 ≡ b1 ∈ Fun A B /\
                forall m ξ (Δ : context m), ren_ok ξ Γ Δ ->
                         forall a0 a1, LR Δ a0 a1 A -> LR Δ (App (ren_tm ξ b0) a0) (App (ren_tm ξ b1) a1) B
  | _ => Γ ⊢ b0 ≡ b1 ∈ A
  end.

Lemma escape {n} (Γ : context n) (a b : tm n) (A : ty) :
  LR Γ a b A -> Γ ⊢ a ≡ b ∈ A.
Proof.
  elim : A n Γ a b=> //=; hauto lq:on ctrs:DEquiv.
Qed.

Definition subst_ok {n m}
  (ρ δ : fin n -> tm m)
  (Γ : context n)
  (Δ : context m) :=
  forall i, LR Δ (ρ i) (δ i) (Γ i).

Definition SEquiv {n} (Γ : context n) (b0 b1 : tm n) (A : ty) :=
  forall m ρ δ (Δ : context m), subst_ok ρ δ Γ Δ ->
                              LR Δ (subst_tm ρ b0) (subst_tm ρ b1) A.

Notation "Γ ⊨ b0 ≡ b1 ∈ A" := (SEquiv Γ b0 b1 A) (at level 70, no associativity).

Lemma soundness {n} (Γ : context n) a A : Γ ⊢ a ∈ A -> Γ ⊨ a ≡ a ∈ A.
Proof.
  move => h.
  elim : n Γ a A / h.
  - rewrite /SEquiv.
    simpl.
Admitted.
