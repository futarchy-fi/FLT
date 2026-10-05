/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudExtensionExists
public import Mathlib.RingTheory.Flat.Localization

/-! # Injective generic coordinates detect surjectivity on geometric points -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [PerfectField K]
  {X Y : FF R K}

/-- The invariant indicator of a missing image detects failure of point surjectivity. -/
theorem GenericGaloisHom.surjective_of_toBialgHom_injective (f : GenericGaloisHom X Y)
    (hf : Function.Injective f.toBialgHom) : Function.Surjective f := by
  classical
  let a : Y.Points →[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] AlgebraicClosure K :=
    ⟨fun y ↦ if y ∈ Set.range f then 0 else 1, by
      intro σ y
      have hs : σ • y ∈ Set.range f ↔ y ∈ Set.range f := by
        constructor
        · rintro ⟨x, hx⟩
          exact ⟨σ⁻¹ • x, by rw [map_smul, hx, inv_smul_smul]⟩
        · rintro ⟨x, rfl⟩
          exact ⟨σ • x, map_smul f σ x⟩
      simp only [hs]
      split <;> simp⟩
  have hz : f.toBialgHom (Y.genericCoordinates a) = 0 := by
    apply (GaloisModule.GenericFiber.genericEvalAlgEquiv K (AlgebraicClosure K)
      (K ⊗[R] X.CoordinateRing)).injective
    ext u
    change u (f.toBialgHom (Y.genericCoordinates a)) = u 0
    rw [map_zero]
    change u (GaloisModule.GenericFiber.canonicalEmbeddingAlgHom K (AlgebraicClosure K)
      (K ⊗[R] X.CoordinateRing) Y.Points (f.comp X.points)
      (Y.genericCoordinates.symm (Y.genericCoordinates a))) = 0
    rw [BialgEquiv.symm_apply_apply,
      GaloisModule.GenericFiber.eval_canonicalEmbeddingAlgHom]
    exact ite_eq_left ⟨X.points (Additive.ofMul u), rfl⟩
  have ha : a = 0 := Y.genericCoordinates.injective (by
    rw [map_zero]
    exact hf (hz.trans (map_zero _).symm))
  intro y
  by_contra hy
  have he := DFunLike.congr_fun ha y
  have hn : y ∉ Set.range f := hy
  change (if y ∈ Set.range f then (0 : AlgebraicClosure K) else 1) = 0 at he
  rw [ite_eq_right hn] at he
  exact one_ne_zero he

/-- Flat extension to the fraction field preserves injectivity of the integral coordinates. -/
theorem ModelHom.genericHom_surjective_of_injective [IsFractionRing R K]
    (f : ModelHom X Y) (hf : Function.Injective f) : Function.Surjective (genericHom f) := by
  let : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  apply GenericGaloisHom.surjective_of_toBialgHom_injective
  rw [ModelHom.toBialgHom_genericHom]
  exact Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
end ThreeAdicPlan
