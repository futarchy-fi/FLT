/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedBoundarySubgroup
public import FLT.Mazur.PolygonCompleteBoundarySubgroupIso
public import FLT.Mazur.CyclicBoundaryParameterSections

/-!
# Actual boundary tests from the original complete subgroup

Independent auxiliary markings on an arbitrary parameter scheme combine with
the original complete cyclic marking. Every cyclic section is the marking of
the actual pulled-back Cartier generator in the unchanged polygon group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonUniversalAction CyclicBoundaryParameter GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "J" => completeClosedFiniteSubgroup K n h
local notation "hP" => completeClosedGenerator_isCartierGenerator K n h

/-- The original closed marking is precisely its original Cartier generator marking. -/
theorem completeClosedBoundaryMarking_cartier (j : Multiplicative (ZMod n)) :
    completeClosedBoundaryMarking K n h j = (J).generatorCurveMarking (hP) j := by
  change _ = (completeClosedGenerator K n h ^ j.toAdd.val) ≫ (J).inclusion
  rw [MonObj.pow_comp, ← completeClosedBoundaryMarking_generator,
    ← completeClosedBoundaryMarking_pow]
  simp only [ZMod.natCast_zmod_val, ofAdd_toAdd]

variable {T : Scheme} (g : T ⟶ Spec (.of K))

/-- All original complete labels as points over an arbitrary boundary test. -/
def completeBoundaryTestMarking : Multiplicative (ZMod n) →* (Over.mk g ⟶ G K n) where
  toFun j := (Over.homMk g (Category.comp_id g) : Over.mk g ⟶ 𝟙_ (Over (Spec (.of K)))) ≫
    completeClosedBoundaryMarking K n h j
  map_one' := by rw [map_one, MonObj.comp_one]
  map_mul' i j := by rw [map_mul, MonObj.comp_mul]

variable (a : UniversalWeierstrass.Labels 4 →* (Over.mk g ⟶ G K n))
  (b : UniversalWeierstrass.Labels 3 →* (Over.mk g ⟶ G K n))

/-- The actual boundary parameter with two independent original auxiliary markings. -/
def completeBoundaryTestParameter : Over.mk g ⟶ CyclicBoundaryParameter.parameter (G K n) n :=
  ofMarkings (G K n) n a b (completeBoundaryTestMarking K n h g)

/-- Every cyclic label recovers its original complete-family value. -/
@[reassoc] theorem completeBoundaryTestParameter_cyclic (j : Multiplicative (ZMod n)) :
    completeBoundaryTestParameter K n h g a b ≫ AuxiliaryLevel.value (G K n) (Label n)
      (1, 1, j) = completeBoundaryTestMarking K n h g j :=
  ofMarkings_cyclic _ _ _ _ _ _

/-- The actual pulled group section retains the entire original marking. -/
theorem completeBoundaryTestParameter_section (j : Multiplicative (ZMod n)) :
    markedSection (G K n) n g (completeBoundaryTestParameter K n h g a b) (1, 1, j) =
      GroupSectionBaseChange.pullSection g (completeClosedBoundaryMarking K n h j) := by
  apply OverPullbackSection.hom_ext
  rw [section_fst, ← Over.comp_left, completeBoundaryTestParameter_cyclic,
    GroupSectionBaseChange.section_fst]
  rfl

/-- The test retains the actual base-changed Cartier generator, with no new subgroup choice. -/
theorem completeBoundaryTestParameter_generator (j : Multiplicative (ZMod n)) :
    markedSection (G K n) n g (completeBoundaryTestParameter K n h g a b) (1, 1, j) =
      ((J).baseChange g).generatorCurveMarking ((hP).baseChange J g) j := by
  rw [completeBoundaryTestParameter_section, completeClosedBoundaryMarking_cartier,
    FiniteSubgroup.generatorCurveMarking_baseChange]
  rfl

/-- The level-four auxiliary marking is retained independently on the parameter scheme. -/
@[reassoc] theorem completeBoundaryTestParameter_four (j : UniversalWeierstrass.Labels 4) :
    completeBoundaryTestParameter K n h g a b ≫ AuxiliaryLevel.value (G K n) (Label n)
      (j, 1, 1) = a j := ofMarkings_four _ _ _ _ _ _

/-- The level-three auxiliary marking is retained independently on the parameter scheme. -/
@[reassoc] theorem completeBoundaryTestParameter_three (j : UniversalWeierstrass.Labels 3) :
    completeBoundaryTestParameter K n h g a b ≫ AuxiliaryLevel.value (G K n) (Label n)
      (1, j, 1) = b j := ofMarkings_three _ _ _ _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
