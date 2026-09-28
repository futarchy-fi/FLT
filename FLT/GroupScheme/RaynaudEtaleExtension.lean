/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRankThreeExtension
public import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Extension from finite étale models

Every generic morphism from a finite étale model over the three-adic integers
extends uniquely, with no restriction on either model's order. Smooth base change
commutes with integral closure, so generic coordinates integral over the base
already lie in the source's integral coordinate algebra. The graph criterion then
constructs the extension.

This treats arbitrary rank étale sources. General three-primary finite flat sources
need not be étale; their rigidity remains a separate arithmetic problem.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- In a smooth algebra over an integrally closed domain, a generic coordinate integral
 over the base already comes from the original algebra. -/
theorem exists_includeRight_eq_of_isIntegral
    {R K A : Type*} [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A]
    (z : K ⊗[R] A) (hz : IsIntegral R z) : ∃ a : A, 1 ⊗ₜ[R] a = z := by
  let e := Algebra.TensorProduct.comm R K A
  let m : A ⊗[R] integralClosure R K →ₐ[A] A ⊗[R] K :=
    Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R K).val
  have hm (t : A ⊗[R] integralClosure R K) : ∃ a : A, m t = a ⊗ₜ[R] (1 : K) := by
    induction t using TensorProduct.inductionOn with
    | tmul a k =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp k.property
      refine ⟨r • a, ?_⟩
      simp only [m, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.val_apply]
      rw [← hr, algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, TensorProduct.add_tmul]⟩
  have hz' : IsIntegral A (e z) := (hz.map e.toAlgHom).tower_top
  obtain ⟨t, ht⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := A) (B := K)).2
      ⟨e z, hz'⟩
  have ht' : m t = e z := congrArg Subtype.val ht
  obtain ⟨a, ha⟩ := hm t
  refine ⟨a, e.injective ?_⟩
  simpa [e] using ha.symm.trans ht'

end Algebra.TensorProduct

namespace ThreeAdicPlan

/-- Every generic coordinate of a morphism from an étale model is integral in its source. -/
theorem GenericGaloisHom.integral_of_etale
    {X Y : FF ℤ_[3] ℚ_[3]} [Algebra.Etale ℤ_[3] X.CoordinateRing]
    (f : GenericGaloisHom X Y) (y : Y.CoordinateRing) :
    ∃ x : X.CoordinateRing, f.toBialgHom (1 ⊗ₜ[ℤ_[3]] y) = 1 ⊗ₜ[ℤ_[3]] x := by
  let g : Y.CoordinateRing →ₐ[ℤ_[3]] ℚ_[3] ⊗[ℤ_[3]] X.CoordinateRing :=
    (f.toBialgHom.toAlgHom.restrictScalars ℤ_[3]).comp Algebra.TensorProduct.includeRight
  have hy : IsIntegral ℤ_[3] (g y) := (Algebra.IsIntegral.isIntegral y).map g
  obtain ⟨x, hx⟩ := Algebra.TensorProduct.exists_includeRight_eq_of_isIntegral (g y) hy
  exact ⟨x, hx.symm⟩

/-- The first graph projection is surjective whenever the source model is étale. -/
theorem GenericGaloisHom.graphFst_surjective_of_etale
    {X Y : FF ℤ_[3] ℚ_[3]} [Algebra.Etale ℤ_[3] X.CoordinateRing]
    (f : GenericGaloisHom X Y) : Function.Surjective f.graphFst :=
  f.graphFst_surjective_of_integral f.integral_of_etale

/-- All generic morphisms from finite étale three-adic models extend uniquely,
regardless of the ranks or exponents of the two models. -/
theorem raynaud_extend_generic_morphism_of_etale
    (X Y : FF ℤ_[3] ℚ_[3]) [Algebra.Etale ℤ_[3] X.CoordinateRing]
    (f : GenericGaloisHom X Y) : ∃! fO : ModelHom X Y, genericHom fO = f :=
  raynaud_extend_generic_morphism_of_graphFst_surjective X Y f f.graphFst_surjective_of_etale

end ThreeAdicPlan
