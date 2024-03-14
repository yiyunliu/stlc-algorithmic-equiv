Require Export syntax.

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

| T_K :
  (* --------- *)
  Γ ⊢ TmK ∈ TyK

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
  A.:Γ ⊢ b0 ≡ b1 ∈ B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  (* ---------------- *)
  Γ ⊢ App (Lam A b0) a0 ≡ subst_tm (a1..) b1 ∈ B
| DE_Ext b0 b1 A B :
  A.:Γ ⊢ App (ren_tm shift b0) (var_tm var_zero) ≡
    App (ren_tm shift b1) (var_tm var_zero) ∈ B ->
  (* ------------------ *)
  Γ ⊢ b0 ≡ b1 ∈ Fun A B
| DE_Unit a b :
  Γ ⊢ a ∈ TyUnit ->
  Γ ⊢ b ∈ TyUnit ->
  (* --------------- *)
  Γ ⊢ a ≡ b ∈ TyUnit
where "Γ ⊢ a ≡ b ∈ A" := (DEquiv Γ a b A).
