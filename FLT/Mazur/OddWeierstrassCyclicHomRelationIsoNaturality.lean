/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomGlobalMarkedRelation
public import FLT.Mazur.OddWeierstrassCyclicHomMarkedGroupRigidity

/-!
# Canonical comparisons agree with specified comparisons and source pullback

Global auxiliary rigidity identifies the constructed comparison with every
specified independently marked comparison. Pullback retains the actual map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)

/-- A specified original comparison is the canonical comparison of equal normalizations. -/
theorem cyclicHomMarkedIso_eq_normalizationRelation
    (h : cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g)
    (e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g))
    (ha : ∀ c : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫
      e.hom.hom.hom.hom = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c) :
    e = cyclicHomNormalizationRelationIso n f g h :=
  cyclicHomMarkedGroupIso_unique n f g e _ ha
    (cyclicHomNormalizationRelationIso_auxiliary n f g h)

/-- Pullback of the canonical actual comparison is the canonical comparison after source change. -/
theorem cyclicHomNormalizationRelationIso_pullback
    (h : cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g)
    {U : Scheme} (k : U ⟶ T)
    (hk : cyclicHomNormalizedPoint n (k ≫ f) = cyclicHomNormalizedPoint n (k ≫ g)) :
    cyclicHomMarkedIsoPullback n f g (cyclicHomNormalizationRelationIso n f g h) k =
      cyclicHomNormalizationRelationIso n (k ≫ f) (k ≫ g) hk :=
  cyclicHomMarkedIso_eq_normalizationRelation n (k ≫ f) (k ≫ g) hk _
    (cyclicHomMarkedIsoPullback_auxiliary n f g _ k
      (cyclicHomNormalizationRelationIso_auxiliary n f g h))

/-- Full normalization equality is equivalent to existence of a unique actual marked comparison. -/
theorem cyclicHom_normalized_eq_iff_existsUnique_marked :
    cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g ↔
      ∃! e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
          auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g),
        (∀ c : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) c ≫
          e.hom.hom.hom.hom = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) c) ∧
        (∀ c : Multiplicative (ZMod n), cyclicHomSourceMarking n f c ≫
          e.hom.hom.hom.hom = cyclicHomSourceMarking n g c) := by
  constructor
  · intro h
    refine ⟨cyclicHomNormalizationRelationIso n f g h,
      ⟨cyclicHomNormalizationRelationIso_auxiliary n f g h,
        cyclicHomNormalizationRelationIso_cyclic n f g h⟩, ?_⟩
    intro e he
    exact cyclicHomMarkedIso_eq_normalizationRelation n f g h e he.1
  · rintro ⟨e, he, _⟩
    exact (cyclicHomGlobalMarkedRelated_iff_normalized_eq n f g).mp ⟨e, he⟩

end FLT.Mazur.OddWeierstrassParameter
