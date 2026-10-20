/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRelationCharpoly
public import FLT.Mazur.SchemeRelationInvariantSpectrum
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral original coordinates from finite free relation fibers

The multiplication polynomial descends coefficient by coefficient to the
actual invariant subring. This constructs integrality of the original source
coordinates. Finite type then gives module finiteness over those invariants.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module Polynomial
namespace FLT.Mazur.AffineRelationCharpoly
open SchemeEffectiveEpiSections
universe u v
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  (e : CategoryTheory.EquivalenceRelation p q) {ι : Type v} [Finite ι]
local notation "C" => compatibleFunctions p q
include e

/-- The whole multiplication polynomial has coefficients in the original invariant ring. -/
theorem exists_invariant_polynomial :
    let _ := p.appTop.hom.toAlgebra
    ∀ (basis : Basis ι Γ(A, ⊤) Γ(D, ⊤)) (s : Γ(A, ⊤)),
      ∃ P : C[X], P.map (C).subtype = relationCharpoly p q basis s ∧
        P.Monic ∧ P.eval₂ (C).subtype s = 0 := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  have hl : relationCharpoly p q basis s ∈ Polynomial.lifts (C).subtype := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, relationCharpoly_invariant p q e basis s n⟩, rfl⟩
  obtain ⟨P, hP⟩ := (mem_lifts _).mp hl
  have he := relationCharpoly_equation p q e basis s
  refine ⟨P, hP, Polynomial.monic_of_injective (f := (C).subtype) Subtype.val_injective ?_, ?_⟩
  · rw [hP]
    exact he.1
  · rw [← eval_map, hP]
    exact he.2

/-- The original invariant inclusion is integral by explicit monic source equations. -/
theorem invariant_inclusion_integral :
    let _ := p.appTop.hom.toAlgebra
    Basis ι Γ(A, ⊤) Γ(D, ⊤) → (C).subtype.IsIntegral := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  obtain ⟨P, _, hm, hz⟩ := exists_invariant_polynomial p q e basis s
  exact ⟨P, hm, hz⟩

/-- Finite type of the source over invariants upgrades these equations to module finiteness. -/
theorem invariant_inclusion_finite (hft : (C).subtype.FiniteType) :
    let _ := p.appTop.hom.toAlgebra
    Basis ι Γ(A, ⊤) Γ(D, ⊤) → (C).subtype.Finite := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis
  exact (invariant_inclusion_integral p q e basis).to_finite hft

end FLT.Mazur.AffineRelationCharpoly
