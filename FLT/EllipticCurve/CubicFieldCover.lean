/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityComparison
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Affine open covers from field-valued factorizations -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u

/-- A family of affine open immersions covers if every algebra-valued point in
every field factors through one member. Residue fields turn this into an actual
scheme cover; checking only rational points of the coefficient field would not suffice. -/
def affineCoverOfFieldLifts {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (f : ∀ i, A →ₐ[R] B i)
    (ho : ∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom (f i).toRingHom)))
    (h : ∀ (K : Type u) [Field K] [Algebra R K] (a : A →ₐ[R] K),
      ∃ i, ∃ b : B i →ₐ[R] K, b.comp (f i) = a) :
    (Spec (.of A)).OpenCover where
  I₀ := ι
  X i := Spec (.of (B i))
  f i := Spec.map (CommRingCat.ofHom (f i).toRingHom)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ho⟩
    intro x
    let K := x.asIdeal.ResidueField
    let a : A →ₐ[R] K := IsScalarTower.toAlgHom R A K
    obtain ⟨i, b, hb⟩ := h K a
    refine ⟨i, PrimeSpectrum.comap b.toRingHom ⟨⊥, inferInstance⟩, ?_⟩
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro z
    change b (f i z) = 0 ↔ z ∈ x.asIdeal
    have hz : b (f i z) = algebraMap A K z := DFunLike.congr_fun hb z
    rw [hz]
    exact Ideal.algebraMap_residueField_eq_zero

end WeierstrassCurve.CubicCharts
