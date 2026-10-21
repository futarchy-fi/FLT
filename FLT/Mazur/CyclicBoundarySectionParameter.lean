/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryMarkingEquivalence
public import FLT.Mazur.CyclicBoundaryOriginalMarkings

/-!
# Independent section markings on unrestricted boundary parameters

Original auxiliary and cyclic homomorphisms in a pulled-back commutative
group give a unique unrestricted parameter with exactly these sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (E : Over S) [GrpObj E] [IsCommMonObj E]
  (n : ℕ) [NeZero n] (g : T ⟶ S)
  (a : Labels 4 →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E))
  (b : Labels 3 →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E))
  (c : Multiplicative (ZMod n) →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E))

/-- The unrestricted parameter retaining the three original section homomorphisms. -/
def ofSectionMarkings : Over.mk g ⟶ parameter E n :=
  liftBoundaryMarking E n g (combinedMarking ((Over.pullback g).obj E) n a b c)

/-- Every full label recovers its original combined section. -/
theorem ofSectionMarkings_section (j : Label n) :
    markedSection E n g (ofSectionMarkings E n g a b c) j =
      a j.1 * b j.2.1 * c j.2.2 :=
  liftBoundaryMarking_section E n g _ j

/-- The independent level-four sections are unchanged. -/
theorem ofSectionMarkings_four (j : Labels 4) :
    markedSection E n g (ofSectionMarkings E n g a b c) (j, 1, 1) = a j := by
  rw [ofSectionMarkings_section, map_one, map_one, _root_.mul_one, _root_.mul_one]

/-- The independent level-three sections are unchanged. -/
theorem ofSectionMarkings_three (j : Labels 3) :
    markedSection E n g (ofSectionMarkings E n g a b c) (1, j, 1) = b j := by
  rw [ofSectionMarkings_section, map_one, map_one, _root_.one_mul, _root_.mul_one]

/-- The entire original cyclic homomorphism is unchanged, including repeated labels. -/
theorem ofSectionMarkings_cyclic :
    cyclicSectionMarking E n g (ofSectionMarkings E n g a b c) = c := by
  apply MonoidHom.ext
  intro j
  rw [cyclicSectionMarking_apply, ofSectionMarkings_section, map_one, map_one,
    _root_.one_mul, _root_.one_mul]

end FLT.Mazur.CyclicBoundaryParameter
