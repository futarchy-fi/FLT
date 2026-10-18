/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompletePinchedMarking
public import FLT.Mazur.CyclicBoundaryParameterSections
public import FLT.Mazur.CyclicBoundaryOriginalMarkings

/-!
# Actual boundary tests from the original complete subgroup

Independent auxiliary markings on an arbitrary parameter scheme combine with
the original complete cyclic marking. Every cyclic section is the marking of
the actual pulled-back Cartier generator in the unchanged polygon group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open CyclicBoundaryParameter GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "G" => PolygonSplitGroup.model K 1
local notation "J" => completePinchedFiniteSubgroup K n labels hlabels
local notation "hP" => completePinchedFiniteSubgroup_generator K n labels hlabels

variable {T : Scheme} (g : T ⟶ Spec (.of K))

/-- All original complete labels as points over an arbitrary boundary test. -/
def completeBoundaryTestMarking : Multiplicative (ZMod n) →* (Over.mk g ⟶ G) where
  toFun j := (Over.homMk g (Category.comp_id g) : Over.mk g ⟶ 𝟙_ (Over (Spec (.of K)))) ≫
    completePinchedBoundaryMarking K n labels hlabels j
  map_one' := by rw [map_one, MonObj.comp_one]
  map_mul' i j := by rw [map_mul, MonObj.comp_mul]

variable (a : UniversalWeierstrass.Labels 4 →* (Over.mk g ⟶ PolygonSplitGroup.model K 1))
  (b : UniversalWeierstrass.Labels 3 →* (Over.mk g ⟶ PolygonSplitGroup.model K 1))

/-- The actual boundary parameter with two independent original auxiliary markings. -/
def completeBoundaryTestParameter : Over.mk g ⟶ CyclicBoundaryParameter.parameter (G) n :=
  ofMarkings (G) n a b (completeBoundaryTestMarking K n labels hlabels g)

/-- Every cyclic label recovers its original complete-family value. -/
@[reassoc] theorem completeBoundaryTestParameter_cyclic (j : Multiplicative (ZMod n)) :
    completeBoundaryTestParameter K n labels hlabels g a b ≫ AuxiliaryLevel.value (G) (Label n)
      (1, 1, j) = completeBoundaryTestMarking K n labels hlabels g j :=
  ofMarkings_cyclic _ _ _ _ _ _

/-- The actual pulled group section retains the entire original marking. -/
theorem completeBoundaryTestParameter_section (j : Multiplicative (ZMod n)) :
    markedSection (G) n g (completeBoundaryTestParameter K n labels hlabels g a b) (1, 1, j) =
      GroupSectionBaseChange.pullSection g
        (completePinchedBoundaryMarking K n labels hlabels j) := by
  apply OverPullbackSection.hom_ext
  rw [section_fst, ← Over.comp_left, completeBoundaryTestParameter_cyclic,
    GroupSectionBaseChange.section_fst]
  rfl

/-- The test retains the actual base-changed Cartier generator, with no new subgroup choice. -/
theorem completeBoundaryTestParameter_generator (j : Multiplicative (ZMod n)) :
    markedSection (G) n g (completeBoundaryTestParameter K n labels hlabels g a b) (1, 1, j) =
      ((J).baseChange g).generatorCurveMarking ((hP).baseChange J g) j := by
  rw [completeBoundaryTestParameter_section, FiniteSubgroup.generatorCurveMarking_baseChange]
  rfl

/-- The level-four auxiliary marking is retained independently on the parameter scheme. -/
@[reassoc] theorem completeBoundaryTestParameter_four (j : UniversalWeierstrass.Labels 4) :
    completeBoundaryTestParameter K n labels hlabels g a b ≫ AuxiliaryLevel.value (G) (Label n)
      (j, 1, 1) = a j := ofMarkings_four _ _ _ _ _ _

/-- The level-three auxiliary marking is retained independently on the parameter scheme. -/
@[reassoc] theorem completeBoundaryTestParameter_three (j : UniversalWeierstrass.Labels 3) :
    completeBoundaryTestParameter K n labels hlabels g a b ≫ AuxiliaryLevel.value (G) (Label n)
      (1, j, 1) = b j := ofMarkings_three _ _ _ _ _ _

end FLT.Mazur.OneGonSmoothing
