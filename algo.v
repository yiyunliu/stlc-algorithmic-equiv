Require Export typing.

Reserved Notation "a ⤳ b" (at level 70, no associativity).
Inductive WRed {n} : tm n -> tm n -> Prop :=
| WR_App b0 b1 a :
  b0 ⤳ b1 ->
  (* ------------- *)
  App b0 a ⤳ App b1 a
| WR_Beta b A a :
  (* ------------- *)
  App (Lam A b) a ⤳ subst_tm (a..) b
where "a ⤳ b" := (WRed a b).

Definition whnf {n} (a : tm n) := forall b, ~ a ⤳ b.

Reserved Notation "a ⇓ v" (at level 70, no associativity).
Inductive WREval {n} : tm n -> tm n -> Prop :=
| E_Step a0 a1 v :
  a0 ⤳ a1 ->
  a1 ⇓ v ->
  (* ------- *)
  a0 ⇓ v
| E_Nf v :
  whnf v ->
  (* ------ *)
  v ⇓ v
where "a ⇓ v" := (WREval a v).

Reserved Notation "Γ ⊢ a ↔ b ∈ A" (at level 70, no associativity).
Reserved Notation "Γ ⊢ a ⇔ b ∈ A" (at level 70, no associativity).
Inductive AEquivTm {n} (Γ : context n) : tm n -> tm n -> ty -> Prop :=
| AET_Base s p t q :
  s ⇓ p ->
  t ⇓ q ->
  Γ ⊢ p ↔ q ∈ TyK ->
  (* ----------- *)
  Γ ⊢ s ⇔ t ∈ TyK
| AET_Arrow s t A B :
  A.:Γ ⊢ App (ren_tm shift s) (var_tm var_zero) ⇔
        App (ren_tm shift t) (var_tm var_zero) ∈ B ->
  (* --------------------- *)
  Γ ⊢ s ⇔ t ∈ Fun A B
| AET_One s t :
  (* ------------------ *)
  Γ ⊢ s ⇔ t ∈ TyUnit
with AEquivPath {n} (Γ : context n) : tm n -> tm n -> ty -> Prop :=
| AEP_Var i :
  Γ ⊢ var_tm i ↔ var_tm i ∈ Γ i
| AEP_App p q s t A B :
  Γ ⊢ p ↔ q ∈ Fun A B ->
  Γ ⊢ s ⇔ t ∈ A ->
  (* ----------------- *)
  Γ ⊢ App p s ↔ App q t ∈ B
| AEP_K :
  Γ ⊢ TmK ↔ TmK ∈ TyK
where "Γ ⊢ a ⇔ b ∈ A" := (AEquivTm Γ a b A)
and  "Γ ⊢ a ↔ b ∈ A" := (AEquivPath Γ a b A).

Scheme AEquivTm_ind' := Induction for AEquivTm Sort Prop
    with AEquivPath_ind' := Induction for AEquivPath Sort Prop.

Combined Scheme algo_mutual_ind from AEquivTm_ind', AEquivPath_ind'.
