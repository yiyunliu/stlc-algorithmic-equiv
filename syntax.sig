tm : Type
ty : Type

Lam : ty -> (tm -> tm) -> tm
App : tm -> tm -> tm
TmK : tm
TmUnit : tm


Fun : ty -> ty -> ty
TyK : ty
TyUnit : ty
