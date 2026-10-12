/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicFamilyRelationNaturality

/-!
# The represented normalization relation is the genuine full marked family relation

This identifies the relation on all source schemes, by restriction to affine
tests and the actual full-marking-compatible comparison in the converse direction.
It concerns the original smooth Weierstrass chart, not the reducible boundary.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicAuxiliaryScheme n).left)

/-- Genuine full marked family comparisons identify the full normalization on every source. -/
theorem CyclicMarkedFamilyRelated.normalized_eq (h : CyclicMarkedFamilyRelated n f g) :
    cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g := by
  apply cyclicSchemeNormalizedPoint_invariant_of_affine_tests
  intro R _ k
  obtain ⟨e, he⟩ := h.pullback n f g k
  exact cyclicProperPresentationRelated_of_affine_family_iso n (k ≫ f) (k ≫ g)
    ((CommGrp.forget (Over (Spec (.of R)))).mapIso e) he

/-- On all source schemes, the actual full marked family relation is normalization equality. -/
theorem cyclicMarkedFamilyRelated_iff_normalized_eq_global :
    CyclicMarkedFamilyRelated n f g ↔
      cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g :=
  ⟨CyclicMarkedFamilyRelated.normalized_eq n f g,
    cyclicMarkedFamilyRelated_of_normalized_eq n f g⟩

/-- The original split kernel pair equates precisely the actual full marked group families. -/
theorem cyclicMarkedFamilyRelated_iff_slice_eq :
    CyclicMarkedFamilyRelated n f g ↔
      f ≫ cyclicNormalizationSliceMap n = g ≫ cyclicNormalizationSliceMap n :=
  (cyclicMarkedFamilyRelated_iff_normalized_eq_global n f g).trans
    (cyclicNormalizationRelation_iff n f g).symm

/-- An actual marked family comparison gives a unique point of the represented relation. -/
theorem cyclicMarkedFamilyRelated_iff_unique_relation_point :
    CyclicMarkedFamilyRelated n f g ↔
      ∃! r : T ⟶ cyclicNormalizationRelation n,
        r ≫ cyclicNormalizationRelationFirst n = f ∧
          r ≫ cyclicNormalizationRelationSecond n = g := by
  rw [cyclicMarkedFamilyRelated_iff_slice_eq]
  constructor
  · intro h
    refine ⟨pullback.lift f g h, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩, ?_⟩
    intro r hr
    apply cyclicNormalizationRelation_hom_ext n
    · exact hr.1.trans (pullback.lift_fst _ _ _).symm
    · exact hr.2.trans (pullback.lift_snd _ _ _).symm
  · rintro ⟨r, hr, _⟩
    rw [← hr.1, ← hr.2, Category.assoc, Category.assoc,
      cyclicNormalizationRelation_condition]

/-- The two actual families over the entire represented relation admit a full marked comparison. -/
theorem cyclicNormalizationRelation_marked_families :
    CyclicMarkedFamilyRelated n (cyclicNormalizationRelationFirst n)
      (cyclicNormalizationRelationSecond n) :=
  (cyclicMarkedFamilyRelated_iff_slice_eq n _ _).mpr (cyclicNormalizationRelation_condition n)

end FLT.Mazur.UniversalWeierstrass
