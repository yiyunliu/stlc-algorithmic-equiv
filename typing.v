Require Export syntax ssrbool ssreflect.
From Hammer Require Import Tactics Hammer.

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
  Γ ⊢ b ⤳* c ∈ A ->
  Γ ⊢ a ⤳* c ∈ A
where "Γ ⊢ a ⤳* b ∈ A" := (Reds Γ a b A).

Fixpoint ne {n} (a : tm n) :=
  match a with
  | var_tm _ => true
  | App a b => ne a
  | Lam _ _ => false
  | TmUnit => false
  | TmK => false
  end.

Definition ren_ok {n m} ξ (Γ : context n) (Δ : context m) :=
  forall i, Γ i = Δ (ξ i).

Fixpoint LR {n} (Γ : context n) (b0 b1 : tm n) (A : ty) : Prop :=
  match A with
  | TyUnit => exists a0 a1, Γ ⊢ b0 ⤳* a0 ∈ TyUnit /\ Γ ⊢ b1 ⤳* a1 ∈ TyUnit /\
                        (ne a0 \/ a0 = TmUnit) /\ (ne a1 \/ a1 = TmUnit)
  | Fun A B => Γ ⊢ b0 ∈ Fun A B /\ Γ ⊢ b1 ∈ Fun A B /\ Γ ⊢ b0 ≡ b1 ∈ Fun A B /\
                forall m ξ (Δ : context m), ren_ok ξ Γ Δ ->
                         forall a0 a1, LR Δ a0 a1 A -> LR Δ (App (ren_tm ξ b0) a0) (App (ren_tm ξ b1) a1) B
  | _ => False
  end.

Lemma red_wt_l n (Γ : context n) (a b : tm n) (A : ty)
  (h : Γ ⊢ a ⤳ b ∈ A) : Γ ⊢ a ∈ A.
Proof. elim : a b A /h; hauto lq:on ctrs:DEquiv, Wt. Qed.

Lemma reds_wt_l n (Γ : context n) (a b : tm n) (A : ty)
  (h : Γ ⊢ a ⤳* b ∈ A) : Γ ⊢ a ∈ A.
Proof. elim : a b A /h; hauto lq:on use:red_wt_l ctrs:DEquiv, Wt. Qed.

Lemma escape {n} (Γ : context n) (a b : tm n) (A : ty) :
  LR Γ a b A -> Γ ⊢ a ≡ b ∈ A /\ Γ ⊢ a ∈ A /\ Γ ⊢ b ∈ A.
Proof.
  elim : A n Γ a b=> //=; hauto l:on use:reds_wt_l ctrs:DEquiv, Wt.
Qed.

Definition subst_ok {n m}
  (ρ δ : fin n -> tm m)
  (Γ : context n)
  (Δ : context m) :=
  forall i, LR Δ (ρ i) (δ i) (Γ i).

Definition SEquiv {n} (Γ : context n) (b0 b1 : tm n) (A : ty) :=
  forall m ρ δ (Δ : context m), subst_ok ρ δ Γ Δ ->
                              LR Δ (subst_tm ρ b0) (subst_tm δ b1) A.

Notation "Γ ⊨ b0 ≡ b1 ∈ A" := (SEquiv Γ b0 b1 A) (at level 70, no associativity).

Lemma lr_sym n (Γ : context n) (b0 b1 : tm n) (A : ty) :
  LR Γ b0 b1 A -> LR Γ b1 b0 A.
Proof.
  elim : A n Γ b0 b1=>//=; qauto l:on ctrs:Wt, DEquiv.
Qed.

Lemma lr_trans n (Γ : context n) (b0 b1 b2 : tm n) (A : ty) :
  LR Γ b0 b1 A -> LR Γ b1 b2 A -> LR Γ b0 b2 A.
Proof.
  elim : A n Γ b0 b1 b2 => //=.
  - move => A ihA B ihB n Γ b0 b1 b2 [h00 h01] [h10 h11].
    repeat split=> /ltac:(try tauto);  first by hauto lq:on ctrs:DEquiv.
    move {h00 h10}.
    move => m ξ Δ h a0 a1 ha.
    have : LR Δ a1 a1 A by hauto lq:on use:lr_sym.
    qauto l:on.
  - hauto lq:on.
Qed.

Lemma lr_left_right_refl n (Γ : context n) a0 a1 A :
  LR Γ a0 a1 A -> LR Γ a0 a0 A /\ LR Γ a1 a1 A.
Proof. hauto lq:on use:lr_sym, lr_trans. Qed.

Lemma ren_ok_id {n} (Γ : context n) :
  ren_ok id Γ Γ.
Proof. sfirstorder. Qed.

Lemma lr_back_clos_left : forall A n (Γ : context n) a0 b0 a1,
    Γ ⊢ a1 ⤳ a0 ∈ A ->
    LR Γ a0 b0 A ->
    LR Γ a1 b0 A.
Proof.
  elim => //=.
  - move => A ihA B ihB n Γ a0 b0 a1 h [h00 h01].
    repeat split.
    + sfirstorder use:red_wt_l.
    + sfirstorder.
    + admit.
    + move => m ξ Δ hξ c0 c1 hc.
      suff : Δ ⊢ App (ren_tm ξ a1) c0 ⤳ App (ren_tm ξ a0) c0 ∈ B by sfirstorder.
      apply R_App with (A := A); last by hauto lq:on use:escape.
      admit.
  - hauto lq:on ctrs:Reds.
Admitted.

Lemma soundness {n} (Γ : context n) a A : Γ ⊢ a ∈ A -> Γ ⊨ a ≡ a ∈ A.
Proof.
  move => h.
  elim : n Γ a A / h.
  - hauto l:on use:lr_left_right_refl unfold:SEquiv.
  - rewrite /SEquiv => n Γ A b B hb ihb m ρ δ Δ hδρ /=.
    split.
    + admit.
    + move => p ξ Ψ hξ a0 a1 ha.
      asimpl.

  - move => n Γ A B b a hb ihb ha iha m ρ δ Δ hρδ //=.
    rewrite /SEquiv in ihb iha.
    move : ihb (hρδ) => /[apply].
    move : iha (hρδ) => /[apply] /=.
    move => iha [ihb0 ihb1].
    move : ihb1 (ren_ok_id Δ)  => /[apply].
    asimpl.
    by apply.
  - hauto l:on.
Admitted.
