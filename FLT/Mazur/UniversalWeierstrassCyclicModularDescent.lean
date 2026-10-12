/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicModularRelation
public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationCoequalizer

/-!
# Descent of maps invariant under genuine full marked family isomorphisms

The split coequalizer now descends exactly the maps invariant under isomorphism
of the original full marked families. Descent is restriction to the original
full closed slice, and it is unique.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
variable (n : ℕ) [NeZero n] {Y : Scheme}
  (v : (cyclicAuxiliaryScheme n).left ⟶ Y)

/-- A map of chart parameters is invariant under genuine full marked family isomorphisms. -/
def CyclicMarkedFamilyInvariant : Prop :=
  ∀ (T : Scheme) (f g : T ⟶ (cyclicAuxiliaryScheme n).left),
    CyclicMarkedFamilyRelated n f g → f ≫ v = g ≫ v

/-- Actual marked-family invariance is exactly the equation for the represented kernel pair. -/
theorem cyclicMarkedFamilyInvariant_iff_relation :
    CyclicMarkedFamilyInvariant n v ↔
      cyclicNormalizationRelationFirst n ≫ v = cyclicNormalizationRelationSecond n ≫ v := by
  constructor
  · intro h
    exact h _ _ _ (cyclicNormalizationRelation_marked_families n)
  · intro h T f g hfg
    have hd := cyclicNormalization_descend n v h
    rw [← hd, ← Category.assoc, ← Category.assoc,
      (cyclicMarkedFamilyRelated_iff_slice_eq n f g).mp hfg]
    simp only [Category.assoc]

/-- Every map invariant under full marked family isomorphisms descends to the full slice. -/
theorem cyclicMarkedFamilyInvariant_descend (h : CyclicMarkedFamilyInvariant n v) :
    cyclicNormalizationSliceMap n ≫ (cyclicNormalizedSliceInclusion n ≫ v) = v :=
  cyclicNormalization_descend n v ((cyclicMarkedFamilyInvariant_iff_relation n v).mp h)

/-- The full slice gives the unique actual scheme-valued descent of every invariant map. -/
theorem cyclicMarkedFamilyInvariant_unique_descent (h : CyclicMarkedFamilyInvariant n v) :
    ∃! d : cyclicNormalizedSlice n ⟶ Y, cyclicNormalizationSliceMap n ≫ d = v := by
  refine ⟨cyclicNormalizedSliceInclusion n ≫ v,
    cyclicMarkedFamilyInvariant_descend n v h, ?_⟩
  intro d hd
  exact cyclicNormalization_descend_unique n v d hd

/-- Every actual map out of the full slice is invariant under marked family isomorphisms. -/
theorem cyclicMarkedFamilyInvariant_of_slice (d : cyclicNormalizedSlice n ⟶ Y) :
    CyclicMarkedFamilyInvariant n (cyclicNormalizationSliceMap n ≫ d) := by
  intro T f g h
  rw [← Category.assoc, ← Category.assoc,
    (cyclicMarkedFamilyRelated_iff_slice_eq n f g).mp h]

end FLT.Mazur.UniversalWeierstrass
