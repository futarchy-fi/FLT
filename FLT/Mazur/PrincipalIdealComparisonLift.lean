/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonoComparisonOpenGluing
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Full comparison arrows off a pulled ideal

Principal lifts glue over the complement of the zero locus of the entire
extended ideal. This includes test-linear combinations of source parameters;
there is no choice of a single common denominator and no finite generation
assumption. The closed complement is described in the actual test spectrum.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.PrincipalIdealComparisonLift
variable {R : Type} [CommRing R] {B C T : Scheme.{0}}
  (w : R →+* Γ(B, ⊤)) (I : Ideal R)

/-- The union of all principal test neighborhoods supplied by the source ideal. -/
def idealOpen : B.Opens := ⨆ a : I, B.basicOpen (w a.val)

/-- Membership uses the whole pulled ideal, including arbitrary test-linear combinations. -/
theorem mem_idealOpen_iff (b : B) :
    b ∈ idealOpen w I ↔ ¬ I.map w ≤ (B.toSpecΓ b).asIdeal := by
  rw [Ideal.map_le_iff_le_comap]
  rw [idealOpen, Opens.mem_iSup]
  simp only [← Scheme.toSpecΓ_preimage_basicOpen]
  constructor
  · rintro ⟨a, ha⟩ h
    exact ha (h a.property)
  · intro h
    obtain ⟨a, ha, hwa⟩ := Set.not_subset.mp h
    exact ⟨⟨a, ha⟩, hwa⟩

/-- The exact closed complement is the zero locus of the full extended ideal. -/
theorem complement_idealOpen :
    (idealOpen w I : Set B)ᶜ =
      B.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus (I.map w : Set Γ(B, ⊤)) := by
  ext b
  change (¬ b ∈ idealOpen w I) ↔ I.map w ≤ (B.toSpecΓ b).asIdeal
  rw [mem_idealOpen_iff, not_not]

/-- Every test-linear combination of the parameters gives a principal subopen. -/
theorem basicOpen_le_idealOpen (b : Γ(B, ⊤)) (hb : b ∈ I.map w) :
    B.basicOpen b ≤ idealOpen w I := by
  intro x hx
  apply (mem_idealOpen_iff w I x).mpr
  intro h
  rw [← Scheme.toSpecΓ_preimage_basicOpen] at hx
  exact hx (h hb)

/-- Every principal local arrow contributes to one unique arrow over this full open. -/
theorem existsUnique_lift (c : C ⟶ T) [Mono c] (t : B ⟶ T)
    (h : ∀ a ∈ I, ∃ d : (B.basicOpen (w a)).toScheme ⟶ C,
      d ≫ c = (B.basicOpen (w a)).ι ≫ t) :
    ∃! d : (idealOpen w I).toScheme ⟶ C, d ≫ c = (idealOpen w I).ι ≫ t :=
  MonoComparisonOpenGluing.existsUnique_on_union c t _ (fun a ↦ h a.val a.property)

end FLT.Mazur.PrincipalIdealComparisonLift
