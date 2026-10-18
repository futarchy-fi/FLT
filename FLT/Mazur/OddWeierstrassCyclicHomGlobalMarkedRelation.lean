/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomMarkedIsoPullback
public import FLT.Mazur.OddWeierstrassCyclicHomLocusNormalizationRelation

/-!
# Global marked comparisons are exactly full normalization equality

Specified genuine comparisons pull back to every affine test. Consequently the
normalization kernel pair represents the global independently marked relation,
without requiring the original source to be affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)

/-- Genuine independent marked comparisons survive arbitrary source change. -/
theorem CyclicHomMarkedFamilyRelated.pullback
    (h : CyclicHomMarkedFamilyRelated n f g) {U : Scheme} (k : U ⟶ T) :
    CyclicHomMarkedFamilyRelated n (k ≫ f) (k ≫ g) := by
  obtain ⟨e, ha, hc⟩ := h
  exact ⟨cyclicHomMarkedIsoPullback n f g e k,
    cyclicHomMarkedIsoPullback_auxiliary n f g e k ha,
    cyclicHomMarkedIsoPullback_cyclic n f g e k hc⟩

/-- Over every source the actual marked relation is precisely full normalization equality. -/
theorem cyclicHomGlobalMarkedRelated_iff_normalized_eq :
    CyclicHomMarkedFamilyRelated n f g ↔
      cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g := by
  constructor
  · intro h
    apply (cyclicHom_affineTests_iff_normalized_eq n f g).mp
    intro R _ k
    exact h.pullback n f g k
  · exact cyclicHomMarkedFamilyRelated_of_normalized_eq n f g

/-- Affine-test comparison existence and global genuine comparison existence coincide. -/
theorem cyclicHomGlobalMarkedRelated_iff_affine_tests :
    CyclicHomMarkedFamilyRelated n f g ↔
      ∀ (R : Type) [CommRing R] (k : Spec (.of R) ⟶ T),
        CyclicHomMarkedFamilyRelated n (k ≫ f) (k ≫ g) := by
  rw [cyclicHomGlobalMarkedRelated_iff_normalized_eq, cyclicHom_affineTests_iff_normalized_eq]

/-- The actual closed-subgroup kernel pair represents the unrestricted global marked relation. -/
theorem cyclicHomLocusRelation_iff_global_marked
    (f g : T ⟶ cyclicHomUniversalMultiplicationLocus n) :
    f ≫ cyclicHomLocusNormalization n = g ≫ cyclicHomLocusNormalization n ↔
      CyclicHomMarkedFamilyRelated n
        (f ≫ cyclicHomUniversalMultiplicationLocusInclusion n)
        (g ≫ cyclicHomUniversalMultiplicationLocusInclusion n) := by
  rw [cyclicHomLocusNormalization_eq_iff, cyclicHomGlobalMarkedRelated_iff_normalized_eq]

end FLT.Mazur.OddWeierstrassParameter
