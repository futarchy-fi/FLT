/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryGeneratorParameter
public import FLT.Mazur.CyclicBoundaryLocusTestSubgroup

/-!
# Original generators identify actual closed boundary subgroups

The closed lift built from a prescribed generator compares its actual
universal subgroup pullback to the original subgroup. The same full curve
comparison retains every independent auxiliary label.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom] (g : T ⟶ S)
  (H : (E.baseChange g).FiniteSubgroup n) {P : 𝟙_ (Over T) ⟶ H.carrier}
  (hP : H.IsCartierGenerator P)
  (a : Labels 4 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))
  (b : Labels 3 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))
local notation "k" => generatorLocusLift E n g H hP a b

/-- The original subgroup is identified with the actual universal subgroup over its closed lift. -/
def generatorLocusSubgroupIso :
    FiniteSubgroup.CompatibleIso H ((unrestrictedLocusSubgroup E n).baseChange (k)) :=
  unrestrictedLocusTestSubgroupIso E n (k) g (generatorParameter E n g H hP a b)
    (generatorLocusLift_inclusion E n g H hP a b) H (generatorParameter_ideal E n g H hP a b)

/-- The actual subgroup comparison retains every original full marking. -/
theorem generatorLocusSubgroupIso_label (j : Label n) :
    (a j.1 * b j.2.1 * H.generatorCurveMarking hP j.2.2) ≫
        (generatorLocusSubgroupIso E n g H hP a b).curve.hom.group =
      GroupSectionBaseChange.pullSection (k) (unrestrictedLocusLabel E n j) := by
  rw [← generatorParameter_label E n g H hP a b j]
  exact unrestrictedLocusTestSubgroupIso_label E n (k) g _ _ H _ j

/-- The independent level-four sections survive the full subgroup comparison. -/
theorem generatorLocusSubgroupIso_four (j : Labels 4) :
    a j ≫ (generatorLocusSubgroupIso E n g H hP a b).curve.hom.group =
      GroupSectionBaseChange.pullSection (k) (unrestrictedLocusLabel E n (j, 1, 1)) := by
  simpa only [map_one, _root_.mul_one] using
    generatorLocusSubgroupIso_label E n g H hP a b (j, 1, 1)

/-- The independent level-three sections survive the full subgroup comparison. -/
theorem generatorLocusSubgroupIso_three (j : Labels 3) :
    b j ≫ (generatorLocusSubgroupIso E n g H hP a b).curve.hom.group =
      GroupSectionBaseChange.pullSection (k) (unrestrictedLocusLabel E n (1, j, 1)) := by
  simpa only [map_one, _root_.one_mul, _root_.mul_one] using
    generatorLocusSubgroupIso_label E n g H hP a b (1, j, 1)

end FLT.Mazur.CyclicBoundaryParameter
