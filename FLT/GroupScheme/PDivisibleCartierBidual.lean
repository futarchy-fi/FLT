/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCartierTatePairing
public import FLT.GroupScheme.PDivisibleVariableHeightHom
public import FLT.GroupScheme.RaynaudBiduality

/-! # The original system morphism into its actual Cartier double dual -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

/-- Double transposition respects the actual integral evaluation equivalences. -/
theorem ModelHom.cartierBidual_naturality {X Y : FF R K} (f : ModelHom X Y)
    (a : Y.CoordinateRing) :
    f.cartierDual.cartierDual (Y.cartierBidualEquiv a) = X.cartierBidualEquiv (f a) := by
  apply WithConv.ext
  ext φ
  rfl

/-- The inverse evaluation equivalences commute with the original integral maps. -/
theorem ModelHom.cartierBidual_symm_naturality {X Y : FF R K} (f : ModelHom X Y)
    (a : Y.cartierDual.cartierDual.CoordinateRing) :
    X.cartierBidualEquiv.symm (f.cartierDual.cartierDual a) =
      f (Y.cartierBidualEquiv.symm a) := by
  apply X.cartierBidualEquiv.injective
  calc
    X.cartierBidualEquiv (X.cartierBidualEquiv.symm (f.cartierDual.cartierDual a)) =
        f.cartierDual.cartierDual a := X.cartierBidualEquiv.apply_symm_apply _
    _ = f.cartierDual.cartierDual (Y.cartierBidualEquiv (Y.cartierBidualEquiv.symm a)) :=
      congrArg f.cartierDual.cartierDual (Y.cartierBidualEquiv.apply_symm_apply a).symm
    _ = X.cartierBidualEquiv (f (Y.cartierBidualEquiv.symm a)) :=
      f.cartierBidual_naturality _

/-- Bidual evaluation is natural as an equality of the actual integral morphisms. -/
theorem ModelHom.toCartierBidual_naturality {X Y : FF R K} (f : ModelHom X Y) :
    f.comp Y.toCartierBidual = X.toCartierBidual.comp f.cartierDual.cartierDual := by
  apply DFunLike.ext
  intro a
  exact (f.cartierBidual_symm_naturality a).symm

namespace PDivisibleSystem
variable [IsLocalRing R]
variable {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- Integral evaluation constructs the system's map into its actual Cartier double dual. -/
def cartierBidualSystemHom : VariableHeightHom X X.cartierDual.cartierDual where
  app n := (X.level n).toCartierBidual
  inclusion_naturality h := (X.inclusion h).toCartierBidual_naturality
  reduction_naturality h := (X.reduction h).toCartierBidual_naturality

/-- The original Tate vectors enter the double dual via the actual integral evaluation map. -/
def cartierBidualTateMap : X.tateSequences →ₗ[ℤ_[p]] X.cartierDual.CartierTate :=
  X.cartierBidualSystemHom.tateMap
end PDivisibleSystem
end ThreeAdicPlan
