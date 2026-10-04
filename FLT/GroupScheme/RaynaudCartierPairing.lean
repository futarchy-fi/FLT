/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierPairingNaturality
public import FLT.GroupScheme.RaynaudDualGenericMap

/-! # Cartier evaluation on the specified original geometric point groups -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

/-- Recover the actual generic coordinate homomorphism of a specified point. -/
def FF.pointCoordinate (X : FF R K) (x : X.Points) :
    K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K := (X.pointsEquiv.symm x).toMul

omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K] in
/-- Original geometric maps are precomposition on the recovered coordinates. -/
theorem ModelHom.pointCoordinate_genericHom {X Y : FF R K} (f : ModelHom X Y)
    (x : X.Points) : Y.pointCoordinate (genericHom f x) =
      (X.pointCoordinate x).comp f.baseChange.toAlgHom := by
  obtain ⟨a, rfl⟩ := X.points_bijective.2 x
  rw [genericHom_points]
  change (Y.pointsEquiv.symm (Y.pointsEquiv _)).toMul =
    (X.pointsEquiv.symm (X.pointsEquiv a)).toMul.comp f.baseChange.toAlgHom
  rw [Y.pointsEquiv.symm_apply_apply, X.pointsEquiv.symm_apply_apply]
  rfl

/-- Dual points evaluated on the actual dual generic coordinate algebra. -/
def FF.dualPointCoordinate (X : FF R K) (y : X.cartierDual.Points) :
    HopfAlgebra.CartierDual K (K ⊗[R] X.CoordinateRing) →ₐ[K] AlgebraicClosure K :=
  (X.cartierDual.pointCoordinate y).comp X.cartierDualGenericEquiv.symm.toAlgEquiv.toAlgHom

/-- Dual point coordinates respect the original transposed integral maps. -/
theorem ModelHom.dualPointCoordinate_genericHom {X Y : FF R K} (f : ModelHom X Y)
    (y : Y.cartierDual.Points) :
    X.dualPointCoordinate (genericHom f.cartierDual y) =
      (Y.dualPointCoordinate y).comp (HopfAlgebra.CartierDual.bialgMap f.baseChange).toAlgHom := by
  unfold FF.dualPointCoordinate
  rw [ModelHom.pointCoordinate_genericHom]
  ext φ
  apply congrArg (Y.cartierDual.pointCoordinate y)
  apply Y.cartierDualGenericEquiv.injective
  change Y.cartierDualGenericEquiv (f.cartierDual.baseChange
    (X.cartierDualGenericEquiv.symm φ)) =
    Y.cartierDualGenericEquiv (Y.cartierDualGenericEquiv.symm
      (HopfAlgebra.CartierDual.bialgMap f.baseChange φ))
  rw [BialgEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun f.cartierDual_baseChange (X.cartierDualGenericEquiv.symm φ)
  change Y.cartierDualGenericEquiv (f.cartierDual.baseChange
    (X.cartierDualGenericEquiv.symm φ)) =
      HopfAlgebra.CartierDual.bialgMap f.baseChange
        (X.cartierDualGenericEquiv (X.cartierDualGenericEquiv.symm φ)) at h
  rw [BialgEquiv.apply_symm_apply] at h
  exact h

/-- The actual finite-level Cartier pairing, valued in geometric units. -/
def FF.cartierPairing (X : FF R K) (y : X.cartierDual.Points) (x : X.Points) :
    (AlgebraicClosure K)ˣ :=
  HopfAlgebra.CartierDual.geometricCharactersEquiv K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing) (X.dualPointCoordinate y) (X.pointCoordinate x)

/-- The finite pairing intertwines original maps and their actual integral transposes. -/
theorem ModelHom.cartierPairing_naturality {X Y : FF R K} (f : ModelHom X Y)
    (y : Y.cartierDual.Points) (x : X.Points) :
    X.cartierPairing (genericHom f.cartierDual y) x = Y.cartierPairing y (genericHom f x) := by
  unfold FF.cartierPairing
  rw [f.dualPointCoordinate_genericHom, f.pointCoordinate_genericHom]
  exact HopfAlgebra.CartierDual.geometricCharactersEquiv_naturality _ _ _

end ThreeAdicPlan
