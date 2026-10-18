/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomMarkedSubgroupRelation
public import FLT.Mazur.CompatibleSubgroupGeneratorOrbitDetection

/-!
# A prescribed Cartier generator determines the full odd cyclic relation

A full compatible comparison preserving the original auxiliary frame and the
chosen generator preserves every original orbit label. Thus the represented
relation also classifies these prescribed-generator comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (hf : cyclicHomMultiplicationEquation n f = 0)
  (hg : cyclicHomMultiplicationEquation n g = 0)
local notation "H" => cyclicHomSubgroup n f hf
local notation "J" => cyclicHomSubgroup n g hg
local notation "P" => orbitGenerator (cyclicHomSubgroup n f hf)
  (cyclicHomSourceMarking n f)   (cyclicHomSubgroup_ideal n f hf)
local notation "Q" => orbitGenerator (cyclicHomSubgroup n g hg)
  (cyclicHomSourceMarking n g)   (cyclicHomSubgroup_ideal n g hg)

/-- Preserving the original Cartier generator preserves every original subgroup orbit label. -/
theorem cyclicHomSubgroupIso_orbit_of_generator (a : CompatibleIso (H) (J))
    (hP : (P) ≫ a.subgroup.hom = (Q)) (i : Multiplicative (ZMod n)) :
    (H).orbitMarking (cyclicHomSourceMarking n f) (cyclicHomSubgroup_ideal n f hf) i ≫
      a.subgroup.hom =
        (J).orbitMarking (cyclicHomSourceMarking n g) (cyclicHomSubgroup_ideal n g hg) i := by
  exact a.orbitMarking_of_generator (cyclicHomSourceMarking n f)
    (cyclicHomSourceMarking n g) (cyclicHomSubgroup_ideal n f hf)
    (cyclicHomSubgroup_ideal n g hg) hP i

/-- The full normalization relation is equivalent to an actual prescribed-generator comparison. -/
theorem cyclicHom_normalized_eq_iff_generator_comparison :
    cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g ↔
      ∃ a : CompatibleIso (H) (J),
        (∀ i : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i ≫
          a.curve.hom.group = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i) ∧
        (P) ≫ a.subgroup.hom = (Q) := by
  constructor
  · intro h
    exact ⟨cyclicHomMarkedRelationSubgroupIso n f g h hf hg,
      cyclicHomMarkedRelationSubgroupIso_auxiliary n f g h hf hg,
      cyclicHomMarkedRelationSubgroupIso_generator n f g h hf hg⟩
  · rintro ⟨a, ha, hP⟩
    exact (cyclicHomMarkedSubgroupRelated_iff_normalized_eq n f g hf hg).mp
      ⟨a, ha, cyclicHomSubgroupIso_orbit_of_generator n f g hf hg a hP⟩

end FLT.Mazur.OddWeierstrassParameter
