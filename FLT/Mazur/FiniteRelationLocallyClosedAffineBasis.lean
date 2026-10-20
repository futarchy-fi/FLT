/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationAffinePrincipalCore
public import FLT.Mazur.LocallyClosedPrincipalNeighborhood
public import FLT.Mazur.SchemeFiniteTargetFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Invariant affine neighborhoods on locally closed finite relation sources

Prime avoidance in the original affine envelope and the whole-relation norm
construct invariant affine neighborhoods. The source itself need not be affine;
in particular it may be an infinitesimal residual rank stage.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteRelationLocallyClosedAffineBasis
set_option backward.isDefEq.respectTransparency false
variable {D A Y Z : Scheme} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [Etale p]
  (j : A ⟶ Y) [IsClosedImmersion j] (k : Y ⟶ Z) [IsOpenImmersion k] [IsAffine Z]

include e j k in
/-- Every whole orbit in an open has an actual invariant affine neighborhood inside it. -/
theorem exists_invariant_affine (W : A.Opens) (x : A)
    (hW : ∀ z : D, p z = x → q z ∈ W) :
    ∃ U : A.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧ p ⁻¹ᵁ U = q ⁻¹ᵁ U := by
  have hf : (p ⁻¹' {x}).Finite :=
    SchemeOpenEnvelope.finite_fiber_of_mem_finiteTarget p x (by
      rw [SchemeOpenEnvelope.finiteTargetOpen_eq_top p]
      trivial)
  obtain ⟨a, ha, hsa, haW⟩ := LocallyClosedPrincipalNeighborhood.exists_affine_principal
    j k W (q '' (p ⁻¹' {x})) (hf.image q) (by
      rintro _ ⟨z, hz, rfl⟩
      exact hW z hz)
  refine ⟨FiniteRelationAffinePrincipalCore.core (p := p) (q := q) a ha,
    FiniteRelationAffinePrincipalCore.core_isAffine a ha, ?_,
    (FiniteRelationAffinePrincipalCore.core_le a ha).trans haW,
    FiniteRelationAffinePrincipalCore.core_invariant e a ha⟩
  apply (FiniteRelationAffinePrincipalCore.mem_core_iff e a ha x).mpr
  intro z hz
  exact hsa ⟨z, hz, rfl⟩

include e j k in
/-- Every point of an invariant open has an invariant affine refinement containing it. -/
theorem exists_invariant_affine_refinement (W : A.Opens)
    (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W) (x : A) (hx : x ∈ W) :
    ∃ U : A.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧ p ⁻¹ᵁ U = q ⁻¹ᵁ U := by
  apply exists_invariant_affine e j k W x
  intro z hz
  have hp : z ∈ p ⁻¹ᵁ W := by
    change p z ∈ W
    rwa [hz]
  rwa [hW] at hp

end FLT.Mazur.FiniteRelationLocallyClosedAffineBasis
