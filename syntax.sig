tm : Type
ty : Type

Lam : ty -> (tm -> tm) -> tm
App : tm -> tm -> tm
TmUnit : tm


Fun : ty -> ty -> ty
TyUnit : ty
