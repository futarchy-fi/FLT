/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisiblePointKernelCotangent
public import Mathlib.GroupTheory.Coset.Basic

/-! # Cotangent coordinates on original square-zero reduction fibers -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (X : PDivisibleSystem R K p height) [∀ n, Finite (X.LevelCotangent n)]
  (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)
  (r : ℕ) (hr : ∀ b : RingHom.ker q, p ^ r • b = 0)

/-- Translate by the specified original lift, then take its actual cotangent functional. -/
def pointFiberCotangentEquiv (a : X.PointColimit B) :
    {x : X.PointColimit B // X.pointColimitMap q x = X.pointColimitMap q a} ≃
      (X.cotangentLimit →ₗ[R] RingHom.ker q) :=
  ((X.pointColimitMapHom q).fiberEquivKer a).trans (X.pointKernelCotangentEquiv q hJ r hr)

/-- The chosen center has zero cotangent coordinate. -/
theorem pointFiberCotangentEquiv_self (a : X.PointColimit B) :
    X.pointFiberCotangentEquiv q hJ r hr a ⟨a, rfl⟩ = 0 := by
  change X.pointKernelCotangentMulEquiv q hJ r hr
    ((X.pointColimitMapHom q).fiberEquivKer a ⟨a, rfl⟩) = 1
  have he : (X.pointColimitMapHom q).fiberEquivKer a ⟨a, rfl⟩ = 1 := by
    apply Subtype.ext
    exact inv_mul_cancel a
  rw [he, map_one]

/-- Reconstruction multiplies the original center by the prescribed infinitesimal correction. -/
theorem pointFiberCotangentEquiv_symm_val (a : X.PointColimit B)
    (v : X.cotangentLimit →ₗ[R] RingHom.ker q) :
    ((X.pointFiberCotangentEquiv q hJ r hr a).symm v).val =
      a * ((X.pointKernelCotangentEquiv q hJ r hr).symm v).val := rfl

/-- Adding a cotangent direction is exactly convolution with its original kernel point. -/
theorem pointFiberCotangentEquiv_mul (a : X.PointColimit B)
    (x : {x : X.PointColimit B // X.pointColimitMap q x = X.pointColimitMap q a})
    (z : (X.pointColimitMapHom q).ker) :
    X.pointFiberCotangentEquiv q hJ r hr a
      ⟨x.val * z.val, by
        rw [X.pointColimitMap_mul, x.property]
        change X.pointColimitMap q a * X.pointColimitMapHom q z.val = _
        rw [z.property, mul_one]⟩ =
      X.pointFiberCotangentEquiv q hJ r hr a x + X.pointKernelCotangentEquiv q hJ r hr z := by
  have he : (X.pointColimitMapHom q).fiberEquivKer a
      ⟨x.val * z.val, by
        change X.pointColimitMapHom q (x.val * z.val) = _
        rw [map_mul, z.property, mul_one]
        exact x.property⟩ = (X.pointColimitMapHom q).fiberEquivKer a x * z := by
    apply Subtype.ext
    exact (mul_assoc _ _ _).symm
  change X.pointKernelCotangentEquiv q hJ r hr
    ((X.pointColimitMapHom q).fiberEquivKer a _) = _
  exact (congrArg (X.pointKernelCotangentEquiv q hJ r hr) he).trans
    (X.pointKernelCotangentEquiv_mul q hJ r hr _ z)

/-- Every original residue fiber has cotangent coordinates when the coefficient map is
surjective and p is nilpotent. The origin is a chosen lift, not an analytic chart. -/
def pointFiberCotangentEquivOfSurjective (hq : Function.Surjective q)
    (hB : IsNilpotent (p : B)) (y : X.PointColimit C) :
    {x : X.PointColimit B // X.pointColimitMap q x = y} ≃
      (X.cotangentLimit →ₗ[R] RingHom.ker q) :=
  (MonoidHom.fiberEquivKerOfSurjective
    (X.pointColimitMap_surjective_squareZero q hq hJ hB) y).trans
      (X.pointKernelCotangentEquiv q hJ r hr)

end ThreeAdicPlan.PDivisibleSystem
