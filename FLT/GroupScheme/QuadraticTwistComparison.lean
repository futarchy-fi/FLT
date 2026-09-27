/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticTwistGenericPoints

/-!
# Cancellation of quadratic Galois signs

The antipode on generic points is negation under any additive comparison.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace HopfAlgebra

universe v
variable {K Ω H A : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [CommRing H] [HopfAlgebra K H] [AddCommGroup A]

/-- Precomposition with the antipode is the inverse for convolution of points. -/
theorem points_antipode_mul (f : H →ₐ[K] Ω) :
    f.comp (antipodeAlgHom K H) * f = 1 := by
  have h := AlgHom.comp_convMul_distrib f
    (WithConv.toConv (antipodeAlgHom K H)) (WithConv.toConv (AlgHom.id K H))
  rw [AlgHom.antipode_id_cancel] at h
  convert h.symm using 1
  · ext x
    change Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x) =
      Algebra.TensorProduct.lmul' K
        (Algebra.TensorProduct.map (f.comp (antipodeAlgHom K H)) f
          (Coalgebra.comul x))
    induction Coalgebra.comul (R := K) x using TensorProduct.inductionOn with
    | add x y hx hy => simp_all
    | tmul x y => rfl
  · ext x
    exact (f.commutes (Coalgebra.counit x)).symm

/-- Every additive comparison takes the antipode of a point to its negative. -/
theorem map_points_antipode (e : Additive (H →ₐ[K] Ω) →+ A) (f : H →ₐ[K] Ω) :
    e (Additive.ofMul (f.comp (antipodeAlgHom K H))) = -e (Additive.ofMul f) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← map_add]
  change e (Additive.ofMul (f.comp (antipodeAlgHom K H) * f)) = 0
  rw [points_antipode_mul]
  exact e.map_zero

end HopfAlgebra

namespace QuadraticTwist

universe v
variable {R H K Ω A : Type v} [CommRing R] [CommRing H] [Field K] [Field Ω]
variable [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
variable [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
variable (u : Rˣ) (r : R) (hr : 2 * r = 1)
variable [Algebra (QuadraticAlgebra R (u : R) 0) Ω]
variable [IsScalarTower R (QuadraticAlgebra R (u : R) 0) Ω]
variable [AddCommGroup A]

local notation "ι" => HopfAlgebra.antipodeAlgEquiv R H
local notation "D" => model (u : R) ι
local notation "s" => IsScalarTower.toAlgHom R (QuadraticAlgebra R (u : R) 0) Ω

omit [Coalgebra.IsCocomm R H] in
/-- Scalar extension of the antipode is the antipode on the generic fibre. -/
theorem generic_antipode :
    Algebra.TensorProduct.map (AlgHom.id K K) (ι).toAlgHom =
      HopfAlgebra.antipodeAlgHom K (K ⊗[R] H) := by
  ext z
  rfl

/-- The inverse generic comparison is equivariant when the coefficients are fixed. -/
theorem genericPointsMulEquiv_symm_fixed
    (σ : Ω →ₐ[K] Ω) (hσ : (σ.restrictScalars R).comp s = s) :
    let := hopfAlgebra (H := H) u r hr
    ∀ f : K ⊗[R] D →ₐ[K] Ω,
      (genericPointsMulEquiv (H := H) u r hr).symm (σ.comp f) =
        σ.comp ((genericPointsMulEquiv (H := H) u r hr).symm f) := by
  let := hopfAlgebra (H := H) u r hr
  dsimp only
  intro f
  apply (genericPointsMulEquiv (H := H) (K := K) (Ω := Ω) u r hr).injective
  rw [MulEquiv.apply_symm_apply, genericPointsMulEquiv_fixed u r hr _ σ hσ,
    MulEquiv.apply_symm_apply]

/-- After an additive comparison, conjugating coefficients inserts exactly one negation. -/
theorem genericPointsMulEquiv_symm_conjugated
    (e : Additive (K ⊗[R] H →ₐ[K] Ω) →+ A)
    (σ : Ω →ₐ[K] Ω)
    (hσ : (σ.restrictScalars R).comp s = (s).comp (conjugation (u : R)).toAlgHom) :
    let := hopfAlgebra (H := H) u r hr
    ∀ f : K ⊗[R] D →ₐ[K] Ω,
      e (Additive.ofMul ((genericPointsMulEquiv (H := H) u r hr).symm (σ.comp f))) =
        -e (Additive.ofMul (σ.comp ((genericPointsMulEquiv (H := H) u r hr).symm f))) := by
  let := hopfAlgebra (H := H) u r hr
  dsimp only
  intro f
  have h := genericPointsMulEquiv_conjugated u r hr
    ((genericPointsMulEquiv (H := H) u r hr).symm f) σ hσ
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h, MulEquiv.symm_apply_apply, generic_antipode]
  exact HopfAlgebra.map_points_antipode e _

end QuadraticTwist
