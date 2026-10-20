/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeInvariantPolynomial
public import FLT.Mazur.LocallyMonicPolynomialEnvelope
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral original coordinates from local finite bases

A monic product of truncations replaces the varying-degree characteristic
polynomial. Its coefficients remain in the unchanged invariant ring, and
its root equation is checked on the original target cover. Neither a global
basis nor a common local rank is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
namespace FLT.Mazur.AffineLocallyFreeRelationCharpoly
open SchemeEffectiveEpiSections LocallyMonicPolynomialEnvelope
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  {ι : Type v} (U : ι → A.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis p (U i)) (hcover : ⨆ i, (U i).1 = ⊤)
  (e : CategoryTheory.EquivalenceRelation p q)
local notation "C" => compatibleFunctions p q
include hU hcover e

/-- Varying ranks still give a globally monic equation over the full original invariants. -/
theorem exists_monic_invariant_polynomial (s : Γ(A, ⊤)) :
    ∃ Q : C[X], Q.Monic ∧ Q.eval₂ (C).subtype s = 0 := by
  obtain ⟨P, hP, hz⟩ := exists_invariant_polynomial p q U hU hcover e s
  refine ⟨envelope P P.natDegree, envelope_monic _ _, ?_⟩
  apply A.sheaf.eq_of_locally_eq' (fun i ↦ (U i).1) ⊤
    (fun _ ↦ homOfLE le_top) (ge_of_eq hcover)
  intro i
  change A.presheaf.map (homOfLE (show (U i).1 ≤ ⊤ from le_top)).op
    ((envelope P P.natDegree).eval₂ (C).subtype s) = _
  apply (ConcreteCategory.bijective_of_isIso (U i).1.topIso.inv).injective
  rw [AffineNormGluing.topIso_inv_global, map_zero, map_zero]
  change (U i).1.ι.appTop.hom ((envelope P P.natDegree).eval₂ (C).subtype s) = 0
  rw [hom_eval₂]
  apply envelope_eval₂_eq_zero
  · rw [← map_map, hP]
    exact relationPolynomial_locally_monic p q U hU hcover (U i) (hU i) s
  · have h := congrArg (U i).1.ι.appTop.hom hz
    rw [hom_eval₂, map_zero] at h
    exact h

/-- The inclusion of the unchanged full invariant ring is integral. -/
theorem invariant_inclusion_integral : (C).subtype.IsIntegral := by
  intro s
  obtain ⟨P, hm, hz⟩ := exists_monic_invariant_polynomial p q U hU hcover e s
  exact ⟨P, hm, hz⟩

/-- Finite type upgrades the constructed integral equations to scalar module finiteness. -/
theorem invariant_inclusion_finite (hft : (C).subtype.FiniteType) : (C).subtype.Finite :=
  (invariant_inclusion_integral p q U hU hcover e).to_finite hft

end FLT.Mazur.AffineLocallyFreeRelationCharpoly
