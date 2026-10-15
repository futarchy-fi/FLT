/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEnvelopeInteriorEquations
public import FLT.Mazur.ValuativeEnvelopeInterior

/-!
# Finite scalar equations detect actual valuation obstructions

Simultaneous vanishing of finitely many original source coefficients is
equivalent to existence of an excluded valuation square centered at the
point. At a full fiber the square is provably unliftable. The equations are
constructed from the denominator ideal; the valuation square is constructed
from specialization, not assumed as part of the equation data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing TopologicalSpace
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {Y X : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens)
  [IsAffine X] [IsLocallyNoetherian X] [NoetherianSpace Y]

/-- A finite system of source equations detects every centered valuation obstruction. -/
theorem exists_finite_valuation_equations :
    ∃ s : Finset Γ(X, ⊤),
      Ideal.span (s : Set Γ(X, ⊤)) = denominatorIdeal π.appTop.hom O ∧
      (∀ x : X, x ∈ fullFiberInterior π O ↔ ∃ r ∈ s, x ∈ X.basicOpen r) ∧
      ∀ x : X, (∀ r ∈ s, r ∈ (X.toSpecΓ x).asIdeal) ↔
        ∃ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x ∧
          D.i₁ (default : Spec (.of D.K)) ∉ O := by
  obtain ⟨s, hs, _, _, ht⟩ := exists_finite_interior_equations π O
  refine ⟨s, hs, ht, fun x ↦ ?_⟩
  rw [← not_interior_iff_valuation, ht]
  simp only [not_exists, not_and]
  exact forall_congr' fun r ↦ forall_congr' fun _ ↦
    (not_mem_basicOpen_iff_sectionPrime r x).symm

omit [IsLocallyNoetherian X] in
/-- At a full closed fiber, vanishing constructs a square with no possible envelope lift. -/
theorem exists_unliftable_of_generator_vanishing
    (s : Set Γ(X, ⊤)) (hs : Ideal.span s = denominatorIdeal π.appTop.hom O)
    (x : X) (hx : x ∈ fullFiberLocus π O)
    (hz : ∀ r ∈ s, r ∈ (X.toSpecΓ x).asIdeal) :
    ∃ D : ValuativeCommSq π, D.i₂ (closedPoint D.R) = x ∧
      D.i₁ (default : Spec (.of D.K)) ∉ O ∧ ¬ D.commSq.HasLift := by
  apply exists_unliftable_valuation π O x hx
  rw [interior_iff_generator π O s hs]
  rintro ⟨r, hr, hxr⟩
  exact (not_mem_basicOpen_iff_sectionPrime r x).mpr (hz r hr) hxr

end FLT.Mazur.SchemeOpenEnvelope
