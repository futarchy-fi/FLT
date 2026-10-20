/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeIntegralCoordinates
public import FLT.Mazur.FiniteProjectiveAffineNorm

/-!
# Original invariant integrality for finite projective relations

Finite projectivity constructs actual local bases of the entire relation.
The invariant monic equations use these bases without assuming a global
basis, constant rank, reduced coefficients, or invariant target charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
namespace FLT.Mazur.FiniteProjectiveRelationIntegralCoordinates
open SchemeEffectiveEpiSections
universe u
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hf : let _ := p.appTop.hom.toAlgebra; Module.Finite Γ(A, ⊤) Γ(D, ⊤))
  (hp : let _ := p.appTop.hom.toAlgebra; Module.Projective Γ(A, ⊤) Γ(D, ⊤))
local notation "C" => compatibleFunctions p q
include hf hp e

/-- Every original source coordinate satisfies a constructed monic invariant equation. -/
theorem exists_monic_invariant_polynomial (s : Γ(A, ⊤)) :
    ∃ P : C[X], P.Monic ∧ P.eval₂ (C).subtype s = 0 :=
  AffineLocallyFreeRelationCharpoly.exists_monic_invariant_polynomial p q
    (FiniteProjectiveAffineNorm.chart p hf hp)
    (FiniteProjectiveAffineNorm.chart_basis p hf hp)
    (FiniteProjectiveAffineNorm.chart_cover p hf hp) e s

/-- Finite projectivity of the full relation makes its original invariant inclusion integral. -/
theorem invariant_inclusion_integral : (C).subtype.IsIntegral := by
  intro s
  exact exists_monic_invariant_polynomial p q e hf hp s

/-- Finite type of the original inclusion then proves scalar module finiteness. -/
theorem invariant_inclusion_finite (hft : (C).subtype.FiniteType) : (C).subtype.Finite :=
  (invariant_inclusion_integral p q e hf hp).to_finite hft

end FLT.Mazur.FiniteProjectiveRelationIntegralCoordinates
