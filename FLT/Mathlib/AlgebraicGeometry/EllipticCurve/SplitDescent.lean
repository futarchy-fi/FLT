/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Aut
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.GaloisDescent
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Henselian
/-!
# Descent of split multiplicative models

Hensel lifting splits the node polynomial over the local field in every residue
characteristic. Its rational roots detect the sign of a geometric isomorphism.
-/

@[expose] public section

open Polynomial IsLocalRing ValuativeRel

/-- A split separable nonconstant reduction supplies a root over a Henselian local ring. -/
theorem Polynomial.exists_root_of_splits_reduction
    {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] (f : R[X]) (hf : f.Monic)
    (hs : (f.map (residue R)).Splits) (hsep : (f.map (residue R)).Separable)
    (hd : (f.map (residue R)).degree ≠ 0) : ∃ a : R, f.IsRoot a := by
  obtain ⟨a, ha⟩ := hs.exists_eval_eq_zero hd
  obtain ⟨a₀, rfl⟩ := residue_surjective a
  have hd0 : (f.map (residue R)).derivative.eval (residue R a₀) ≠ 0 := by
    exact hsep.eval₂_derivative_ne_zero (RingHom.id _) (by simpa using ha)
  obtain ⟨b, hb, -⟩ := HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀
    (by
      apply (residue_eq_zero_iff _).mp
      simpa only [eval_map, eval₂_at_apply] using ha)
    (by
      change IsUnit (residue R (f.derivative.eval a₀))
      apply isUnit_iff_ne_zero.mpr
      change (residue R) (f.derivative.eval a₀) ≠ 0
      simpa only [derivative_map, eval_map, eval₂_at_apply] using hd0)
  exact ⟨b, hb⟩

/-- The monicity assumption in Hensel lifting can be replaced by a unit leading coefficient. -/
theorem Polynomial.exists_root_of_splits_reduction_of_isUnit_leadingCoeff
    {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] (p : R[X]) (hu : IsUnit p.leadingCoeff)
    (hs : (p.map (residue R)).Splits) (hsep : (p.map (residue R)).Separable)
    (hd : (p.map (residue R)).degree ≠ 0) : ∃ a : R, p.IsRoot a := by
  let u := hu.unit
  let f := C (↑u⁻¹ : R) * p
  have hm : f.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (by simp [u])
  have hunit : IsUnit (residue R (↑u⁻¹ : R)) := u⁻¹.isUnit.map _
  have hfm : f.map (residue R) = C (residue R (↑u⁻¹ : R)) * p.map (residue R) := by
    simp only [f, Polynomial.map_mul, map_C]
  obtain ⟨a, ha⟩ := f.exists_root_of_splits_reduction hm
    (by rw [hfm]; exact (Splits.C _).mul hs)
    (by rw [hfm]; exact Separable.unit_mul (hunit.map C) hsep)
    (by rw [hfm, degree_C_mul hunit.ne_zero]; exact hd)
  refine ⟨a, ?_⟩
  have h : (↑u⁻¹ : R) * p.eval a = 0 := by simpa only [IsRoot, f, eval_mul, eval_C] using ha
  exact (u⁻¹.isUnit.mul_right_eq_zero).mp h

namespace WeierstrassCurve
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A split multiplicative model has a rational root of its node polynomial. -/
theorem exists_root_nodePoly_of_hasSplitMultiplicativeReduction
    (E : WeierstrassCurve K) [E.HasSplitMultiplicativeReduction 𝒪[K]] :
    ∃ a : K, E.nodePoly.IsRoot a := by
  let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  let W := E.integralModel 𝒪[K]
  have hc : IsUnit W.c₄ := (residue_ne_zero_iff_isUnit _).mp
    (E.residue_integralModel_c₄_ne_zero 𝒪[K])
  have hl : W.nodePoly.leadingCoeff = W.c₄ := by
    simpa only [nodePoly, sub_eq_add_neg, ← map_neg] using
      (leadingCoeff_quadratic (b := W.a₁ * W.c₄)
        (c := -(54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) hc.ne_zero)
  obtain ⟨a, ha⟩ := W.nodePoly.exists_root_of_splits_reduction_of_isUnit_leadingCoeff
    (hl ▸ hc) HasSplitMultiplicativeReduction.splitMultiplicativeReduction
    (E.separable_nodePoly_map 𝒪[K])
    (degree_ne_of_natDegree_ne (by
      change (W.nodePoly.map (algebraMap 𝒪[K] (ResidueField 𝒪[K]))).natDegree ≠ 0
      rw [E.natDegree_nodePoly_map 𝒪[K]]; norm_num))
  refine ⟨algebraMap 𝒪[K] K a, ?_⟩
  have he : W.map (algebraMap 𝒪[K] K) = E := by
    ext <;> simp [W, integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq,
      integralModel_a₄_eq, integralModel_a₆_eq]
  rw [← he, map_nodePoly]
  simp only [IsRoot, eval_map, eval₂_at_apply, ha.eq_zero, map_zero]

/-- The node polynomial of a split multiplicative model splits over the local field. -/
theorem nodePoly_splits_of_hasSplitMultiplicativeReduction
    (E : WeierstrassCurve K) [E.HasSplitMultiplicativeReduction 𝒪[K]] :
    E.nodePoly.Splits := by
  obtain ⟨a, ha⟩ := E.exists_root_nodePoly_of_hasSplitMultiplicativeReduction
  have hc : E.c₄ ≠ 0 := by
    intro h
    have he := integralModel_c₄_eq 𝒪[K] E
    have hz : (E.integralModel 𝒪[K]).c₄ = 0 :=
      (IsFractionRing.injective 𝒪[K] K) (he.trans (h.trans (map_zero _).symm))
    exact E.residue_integralModel_c₄_ne_zero 𝒪[K] (by rw [hz, map_zero])
  apply Splits.of_natDegree_eq_two (x := a) _ ha
  simpa only [nodePoly, sub_eq_add_neg, ← map_neg] using
    (natDegree_quadratic (b := E.a₁ * E.c₄)
      (c := -(54 * E.b₆ - 3 * E.b₂ * E.b₄ + E.a₂ * E.c₄)) hc)
end WeierstrassCurve
