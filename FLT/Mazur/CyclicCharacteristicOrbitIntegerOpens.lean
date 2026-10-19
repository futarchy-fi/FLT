/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantPrincipal
public import FLT.Mazur.CyclicCharacteristicOrbitFiniteQuotient

/-!
# Actual characteristic opens of the full orbit quotient

Integer unit loci are saturated for the full comparison relation. Their inverse
images in each original normalized chart are the usual integer-invertible opens.
The two characteristic opens cover the actual orbit space.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The integer-invertible open in the actual full comparison orbit space. -/
def integerOpen (m : ℕ) : Opens (Orbit n) :=
  invariantPrincipal n ⊤ (m : (invariantSheaf n).obj.obj (op ⊤))

/-- Its inverse image is the original source integer-invertible open. -/
theorem pullOpen_integerOpen (m : ℕ) :
    (pullOpen n (integerOpen n m)).val =
      CharacteristicTwoThree.unitOpen (normalizedDisjointSource n) m := by
  rw [integerOpen, pullOpen_invariantPrincipal]
  simp only [map_natCast]
  rfl

/-- Test membership in an integer orbit open on any original normalized representative. -/
theorem mem_integerOpen_iff (m : ℕ) (b : Bool) (x : normalizedLocus n b) :
    projection n (normalizedDisjointInclusion n b x) ∈ integerOpen n m ↔
      x ∈ CharacteristicTwoThree.unitOpen (normalizedLocus n b) m := by
  change normalizedDisjointInclusion n b x ∈ (pullOpen n (integerOpen n m)).val ↔ _
  rw [pullOpen_integerOpen]
  change x ∈ (normalizedDisjointInclusion n b) ⁻¹ᵁ
    (normalizedDisjointSource n).basicOpen (m : Γ(normalizedDisjointSource n, ⊤)) ↔ _
  rw [Scheme.preimage_basicOpen_top, map_natCast]
  rfl

/-- Every normalized component maps into the open for its own auxiliary integer. -/
theorem normalized_mem_integerOpen (b : Bool) (x : normalizedLocus n b) :
    projection n (normalizedDisjointInclusion n b x) ∈ integerOpen n (chartInteger b) := by
  rw [mem_integerOpen_iff]
  change x ∈ (normalizedLocus n b).basicOpen _
  rw [(normalizedLocus n b).basicOpen_of_isUnit (normalizedLocus_chartInteger_isUnit n b)]
  trivial

/-- Two and three give an actual open cover of the full orbit space. -/
theorem integerOpen_two_sup_three : integerOpen n 2 ⊔ integerOpen n 3 = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨x, rfl⟩ := projection_surjective n z
  obtain ⟨b, y, rfl⟩ := normalizedDisjointSource_covers n x
  have h := normalized_mem_integerOpen n b y
  cases b
  · exact Or.inl h
  · exact Or.inr h

/-- Full comparison arrows retain the integer unit loci, including residual stabilizers. -/
theorem integerOpen_saturated (m : ℕ) (a : disjointComparisonArrows n) :
    disjointComparisonSource n a ∈ (pullOpen n (integerOpen n m)).val ↔
      disjointComparisonTarget n a ∈ (pullOpen n (integerOpen n m)).val := by
  change projection n (disjointComparisonSource n a) ∈ integerOpen n m ↔
    projection n (disjointComparisonTarget n a) ∈ integerOpen n m
  rw [projection_pair]

end FLT.Mazur.CyclicCharacteristicOrbit
