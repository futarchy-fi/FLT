/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationOriginalNormCore
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Constructed original invariant principal neighborhoods

Prime avoidance and the whole original finite-flat norm give nonvanishing
invariant parameters around every orbit in an open. No basis or invariant
parameter is supplied. Compact invariant opens have finite such covers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.FiniteRelationInvariantNeighborhoods
open SchemeEffectiveEpiSections FiniteFlatRelationNormCoefficient
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{0}} [IsAffine A] (p q : D ⟶ A)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)

include e

/-- Every whole orbit in an original open has a constructed nonvanishing invariant parameter. -/
theorem exists_principal (U : A.Opens) (x : A)
    (hx : ∀ z : D, p z = x → q z ∈ U) :
    ∃ s : compatibleFunctions p q, x ∈ A.basicOpen s.val ∧ A.basicOpen s.val ≤ U := by
  let _ : IsAffine D := isAffine_of_isAffineHom p
  obtain ⟨a, ha, haU⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    U (q '' (p ⁻¹' {x})) ((p.finite_preimage_singleton x).image q) (by
      rintro _ ⟨z, hz, rfl⟩
      exact hx z hz)
  refine ⟨coefficient p q e a, ?_,
    (FiniteRelationOriginalNormCore.basicOpen_coefficient_le p q e a).trans haU⟩
  apply (mem_basicOpen_coefficient p q e a x).mpr
  intro z hz
  exact ha ⟨z, hz, rfl⟩

/-- Stable original opens have enough invariant principal neighborhoods at every point. -/
theorem exists_principal_of_invariant (U : A.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U)
    (x : A) (hx : x ∈ U) :
    ∃ s : compatibleFunctions p q, x ∈ A.basicOpen s.val ∧ A.basicOpen s.val ≤ U := by
  apply exists_principal p q e U x
  intro z hz
  have hp : z ∈ p ⁻¹ᵁ U := by
    change p z ∈ U
    rwa [hz]
  rw [hU] at hp
  exact hp

/-- A compact invariant original domain is covered by finitely many original invariant scalars. -/
theorem exists_finite_principal_cover (U : A.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U)
    (hcompact : IsCompact (U : Set A)) :
    ∃ T : Finset (compatibleFunctions p q),
      (∀ s ∈ T, A.basicOpen s.val ≤ U) ∧ (⨆ s : T, A.basicOpen s.val.val) = U := by
  classical
  let I := {s : compatibleFunctions p q // A.basicOpen s.val ≤ U}
  have hc : (U : Set A) ⊆ ⋃ s : I, (A.basicOpen s.val.val : Set A) := by
    intro x hx
    obtain ⟨s, hs, hsU⟩ := exists_principal_of_invariant p q e U hU x hx
    exact Set.mem_iUnion.mpr ⟨⟨s, hsU⟩, hs⟩
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover
    (fun s : I ↦ (A.basicOpen s.val.val : Set A)) (fun s ↦ (A.basicOpen s.val.val).isOpen) hc
  refine ⟨t.image Subtype.val, ?_, le_antisymm ?_ ?_⟩
  · intro s hs
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hs
    exact r.property
  · apply iSup_le
    intro s
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp s.property
    exact hr ▸ r.property
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨⟨s.val, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩, hxs⟩

end FLT.Mazur.FiniteRelationInvariantNeighborhoods
