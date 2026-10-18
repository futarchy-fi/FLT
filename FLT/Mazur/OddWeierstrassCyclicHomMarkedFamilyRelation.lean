/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomAffinePresentationInvariant
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationRelationIso

/-!
# The independent marked relation and its affine-local descent

The relation asks for genuine group isomorphisms preserving the two original
markings. Affine-local comparisons identify normalization and construct a
single marked comparison over the unchanged original source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)

/-- The original independent auxiliary and cyclic markings have a genuine group comparison. -/
def CyclicHomMarkedFamilyRelated : Prop :=
  ∃ e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g),
    (∀ c : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫
      e.hom.hom.hom.hom = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c) ∧
    (∀ c : Multiplicative (ZMod n), cyclicHomSourceMarking n f c ≫ e.hom.hom.hom.hom =
      cyclicHomSourceMarking n g c)

/-- Equality of complete normalized parameters constructs an original marked group comparison. -/
theorem cyclicHomMarkedFamilyRelated_of_normalized_eq
    (h : cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g) :
    CyclicHomMarkedFamilyRelated n f g :=
  ⟨cyclicHomNormalizationRelationIso n f g h,
    cyclicHomNormalizationRelationIso_auxiliary n f g h,
    cyclicHomNormalizationRelationIso_cyclic n f g h⟩

/-- On affine sources the genuine independent marked relation is exactly normalization equality. -/
theorem cyclicHomMarkedFamilyRelated_iff_normalized_eq [IsAffine T] :
    CyclicHomMarkedFamilyRelated n f g ↔
      cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g := by
  constructor
  · rintro ⟨e, ha, hc⟩
    exact cyclicHomNormalizedPoint_invariant_of_affine_iso n f g
      ((CommGrp.forget (Over T)).mapIso e) ha hc
  · exact cyclicHomMarkedFamilyRelated_of_normalized_eq n f g

/-- Actual marked comparisons on every affine test are equivalent to full normalization equality. -/
theorem cyclicHom_affineTests_iff_normalized_eq :
    (∀ (R : Type) [CommRing R] (k : Spec (.of R) ⟶ T),
      CyclicHomMarkedFamilyRelated n (k ≫ f) (k ≫ g)) ↔
      cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g := by
  constructor
  · intro h
    apply cyclicHomNormalizedPoint_invariant_of_affine_tests n f g
    intro R _ k
    obtain ⟨e, ha, hc⟩ := h R k
    exact cyclicHomProperRelated_of_affine_iso n _ _
      ((CommGrp.forget _).mapIso e) ha hc
  · intro h R _ k
    apply cyclicHomMarkedFamilyRelated_of_normalized_eq
    rw [cyclicHomNormalizedPoint_natural, cyclicHomNormalizedPoint_natural, h]

/-- Affine-local genuine comparison data give a global original marked family comparison. -/
theorem cyclicHomMarkedFamilyRelated_of_affine_tests
    (h : ∀ (R : Type) [CommRing R] (k : Spec (.of R) ⟶ T),
      CyclicHomMarkedFamilyRelated n (k ≫ f) (k ≫ g)) :
    CyclicHomMarkedFamilyRelated n f g :=
  cyclicHomMarkedFamilyRelated_of_normalized_eq n f g
    ((cyclicHom_affineTests_iff_normalized_eq n f g).mp h)

end FLT.Mazur.OddWeierstrassParameter
