/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomGlobalMarkedRelation
public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationRelationOrbit

/-!
# The odd represented relation classifies actual marked subgroup comparisons

The converse uses the actual subgroup inclusion to recover each original
cyclic section. Normalization equality is a conclusion of the full compatible
comparison, including over nonaffine bases with coincident orbit labels.
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

/-- The relation asks for an actual full comparison retaining both independent markings. -/
def CyclicHomMarkedSubgroupRelated : Prop :=
  ∃ a : CompatibleIso (H) (J),
    (∀ i : Labels 3, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i ≫
      a.curve.hom.group = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i) ∧
    (∀ i : Multiplicative (ZMod n),
      (H).orbitMarking (cyclicHomSourceMarking n f) (cyclicHomSubgroup_ideal n f hf) i ≫
        a.subgroup.hom =
      (J).orbitMarking (cyclicHomSourceMarking n g) (cyclicHomSubgroup_ideal n g hg) i)

/-- Actual subgroup label equations recover the original smooth-group label equations. -/
theorem cyclicHomMarkedSubgroupRelated_family
    (h : CyclicHomMarkedSubgroupRelated n f g hf hg) :
    CyclicHomMarkedFamilyRelated n f g := by
  obtain ⟨a, ha, hc⟩ := h
  let e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g) :=
    CommGrp.mkIso (groupIso a.curve) (IsMonHom.one_hom a.curve.hom.group)
      (IsMonHom.mul_hom a.curve.hom.group)
  refine ⟨e, ha, fun i ↦ ?_⟩
  change cyclicHomSourceMarking n f i ≫ a.curve.hom.group = cyclicHomSourceMarking n g i
  have hi := congrArg (fun z ↦ z ≫ (J).inclusion) (hc i)
  rw [Category.assoc, ← a.group_inclusion, ← Category.assoc,
    orbitMarking_inclusion, orbitMarking_inclusion] at hi
  exact hi

/-- Full normalization equality is precisely existence of an actual fully marked comparison. -/
theorem cyclicHomMarkedSubgroupRelated_iff_normalized_eq :
    CyclicHomMarkedSubgroupRelated n f g hf hg ↔
      cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g := by
  constructor
  · intro h
    exact (cyclicHomGlobalMarkedRelated_iff_normalized_eq n f g).mp
      (cyclicHomMarkedSubgroupRelated_family n f g hf hg h)
  · intro h
    exact ⟨cyclicHomMarkedRelationSubgroupIso n f g h hf hg,
      cyclicHomMarkedRelationSubgroupIso_auxiliary n f g h hf hg,
      cyclicHomMarkedRelationSubgroupIso_orbit n f g h hf hg⟩

/-- Genuine marked group comparison also supplies a full compatible subgroup comparison. -/
theorem cyclicHomMarkedSubgroupRelated_iff_family :
    CyclicHomMarkedSubgroupRelated n f g hf hg ↔ CyclicHomMarkedFamilyRelated n f g := by
  rw [cyclicHomMarkedSubgroupRelated_iff_normalized_eq,
    cyclicHomGlobalMarkedRelated_iff_normalized_eq]

/-- The actual kernel pair represents full marked original subgroup comparisons. -/
theorem cyclicHomLocusRelation_iff_marked_subgroup
    (q r : T ⟶ cyclicHomUniversalMultiplicationLocus n)
    (hq : cyclicHomMultiplicationEquation n
      (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n) = 0)
    (hr : cyclicHomMultiplicationEquation n
      (r ≫ cyclicHomUniversalMultiplicationLocusInclusion n) = 0) :
    q ≫ cyclicHomLocusNormalization n = r ≫ cyclicHomLocusNormalization n ↔
      CyclicHomMarkedSubgroupRelated n
        (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n)
        (r ≫ cyclicHomUniversalMultiplicationLocusInclusion n) hq hr := by
  rw [cyclicHomLocusNormalization_eq_iff, cyclicHomMarkedSubgroupRelated_iff_normalized_eq]

end FLT.Mazur.OddWeierstrassParameter
