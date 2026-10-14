/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldSubgroup
public import FLT.Mazur.RelativeCyclicSubgroupComparison

/-!
# The original field divisor has its original faithful cyclic presentation

The full original field marking, with its proved group law, presents the
actual product divisor. The comparison retains every original labeled section
and its Cartier generator rather than choosing a new abstract cyclic subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve UniversallyDistinctSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "S" => Spec (CommRingCat.of L)
local notation "E" => completeFieldGeneralizedCurve K n h L a ha p q hs (0 : Fin n)
local notation "φ" => completeFieldCyclicPointHom K n h L a ha p q hs
local notation "H" => completeFieldFiniteSubgroup K n h L a ha p q hs

/-- The proved full field group marking remains universally distinct on all test schemes. -/
theorem completeFieldCyclicPointHom_distinct :
    UniversallyDistinct (fun i : ZMod n ↦ (φ) (.ofAdd i)) := by
  simpa only [completeFieldCyclicPointHom_apply, toAdd_ofAdd] using
    completeCyclicSection_universallyDistinct K n h s p q hs

local notation "hφ" => completeFieldCyclicPointHom_distinct K n h L a ha p q hs

/-- The faithful marking presents the actual original divisor in the full DR curve. -/
def completeFieldMarkedSubgroupIso : FiniteSubgroup.CompatibleIso
    ((E).relativeCyclicSubgroup (φ) (hφ)) H := by
  let _ := completeCyclicDivisorCommGrpObj K n h s p q hs
  let _ := completeFieldCommGrp K n h L a ha p q hs (0 : Fin n)
  refine
    { curve := Iso.refl E
      subgroup := completeCyclicDivisorIso K n h s p q hs
      isMonHom := inferInstance
      compatible := ?_ }
  change (ConstantCyclicSectionMap.toScheme (φ) ≫ (E).inclusion) ≫ 𝟙 (E).curve =
    (completeCyclicDivisorIso K n h s p q hs).hom ≫ (H).curveMap
  erw [Category.comp_id, completeFieldGeneralizedCurve_inclusion K n h L a ha p q hs,
    Category.comp_id, completeFieldCyclicPointHom_toScheme K n h L a ha p q hs]
  apply Over.OverMorphism.ext
  rw [Over.comp_left, completeFieldFiniteSubgroup_curveMap]
  exact (completeCyclicDivisorSchemeIso_ι K n h s p q hs).symm

/-- The presented generator is exactly the original generator of the complete product divisor. -/
theorem completeFieldMarkedSubgroupIso_generator :
    (E).relativeCyclicGenerator (φ) (hφ) ≫
      (completeFieldMarkedSubgroupIso K n h L a ha p q hs).subgroup.hom =
        completeFieldGenerator K n h L a ha p q hs := rfl

/-- Every labeled section retains its exact original map into the complete square. -/
theorem completeFieldMarkedSubgroupIso_section (i : ZMod n) :
    (ConstantCyclicGroup.component S n i ≫
      (completeFieldMarkedSubgroupIso K n h L a ha p q hs).subgroup.hom ≫ (H).curveMap).left =
        completeCartesianMarking K n h s p q hs ((ZMod.finEquiv n).symm i) := by
  rw [Over.comp_left, Over.comp_left, completeFieldFiniteSubgroup_curveMap]
  change (ConstantCyclicGroup.component S n i).left ≫
    (completeCyclicDivisorSchemeIso K n h s p q hs).hom ≫
      ((completeMarkingDivisor K n h).comap p).subschemeι = _
  rw [completeCyclicDivisorSchemeIso_ι, ← Over.comp_left, completeCyclicMarking_component]
  rfl

/-- The faithful presentation retains the original entire product ideal. -/
theorem completeFieldMarkedSubgroup_ideal :
    ((E).relativeCyclicSubgroup (φ) (hφ)).ideal =
      (completeMarkingDivisor K n h).comap p := by
  let _ := completeFieldCommGrp K n h L a ha p q hs (0 : Fin n)
  change (ConstantCyclicSectionMap.toScheme (φ) ≫ (E).inclusion).left.ker = _
  erw [completeFieldGeneralizedCurve_inclusion K n h L a ha p q hs, Category.comp_id,
    completeFieldCyclicPointHom_toScheme K n h L a ha p q hs, completeCyclicMarking_originalIdeal]

end FLT.Mazur.PolygonInfinitesimalStages
