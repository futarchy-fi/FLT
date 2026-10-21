/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundarySectionParameter
public import FLT.Mazur.CyclicBoundaryUnrestrictedTestLocus

/-!
# Original Cartier generators give closed unrestricted boundary tests

A generator of an original subgroup and two independently chosen auxiliary
markings give an actual map to the closed multiplication locus. Its original
full orbit ideal agrees with the original subgroup, with all multiplicities.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  (g : T ⟶ S)
  (H : (E.baseChange g).FiniteSubgroup n) {P : 𝟙_ (Over T) ⟶ H.carrier}
  (hP : H.IsCartierGenerator P)
  (a : Labels 4 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))
  (b : Labels 3 →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))

/-- The original generator and original auxiliary markings determine the parameter. -/
def generatorParameter : Over.mk g ⟶ parameter E.group n :=
  ofSectionMarkings E.group n g a b (H.generatorCurveMarking hP)

/-- Its entire cyclic marking is the original generator homomorphism. -/
theorem generatorParameter_cyclic :
    cyclicSectionMarking E.group n g (generatorParameter E n g H hP a b) =
      H.generatorCurveMarking hP :=
  ofSectionMarkings_cyclic E.group n g a b _

/-- The original full subgroup ideal is exactly the orbit of this actual parameter. -/
theorem generatorParameter_ideal :
    H.ideal = (E.baseChange g).cyclicMarkingIdeal
      (cyclicSectionMarking E.group n g (generatorParameter E n g H hP a b)) := by
  rw [generatorParameter_cyclic]
  exact (H.generatorCurveMarking_ideal (E.baseChange g) hP).symm

variable [SmoothOfRelativeDimension 1 E.group.hom]

/-- The constructed parameter lies in the closed multiplication locus. -/
def generatorLocusLift : T ⟶ unrestrictedMultiplicationLocus E n :=
  unrestrictedTestLocusLift E n g (generatorParameter E n g H hP a b) H
    (generatorParameter_ideal E n g H hP a b)

/-- The closed lift retains the complete parameter and both original auxiliary markings. -/
@[reassoc] theorem generatorLocusLift_inclusion :
    generatorLocusLift E n g H hP a b ≫ unrestrictedMultiplicationLocusInclusion E n =
      (generatorParameter E n g H hP a b).left :=
  unrestrictedTestLocusLift_inclusion E n g _ H _

/-- There is exactly one closed lift of the prescribed original full parameter. -/
theorem generatorLocusLift_unique (k : T ⟶ unrestrictedMultiplicationLocus E n)
    (hk : k ≫ unrestrictedMultiplicationLocusInclusion E n =
      (generatorParameter E n g H hP a b).left) :
    k = generatorLocusLift E n g H hP a b :=
  unrestrictedTestLocusLift_unique E n g _ H _ k hk

omit [SmoothOfRelativeDimension 1 E.group.hom] in
/-- Every auxiliary and cyclic label remains its original group section. -/
theorem generatorParameter_label (j : Label n) :
    markedSection E.group n g (generatorParameter E n g H hP a b) j =
      a j.1 * b j.2.1 * H.generatorCurveMarking hP j.2.2 :=
  ofSectionMarkings_section E.group n g a b _ j

end FLT.Mazur.CyclicBoundaryParameter
