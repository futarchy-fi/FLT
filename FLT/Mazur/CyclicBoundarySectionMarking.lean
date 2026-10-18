/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryParameterSections
public import FLT.Mazur.GroupMarkingBaseChange

/-!
# Boundary sections form the original label homomorphisms

The actual parameter sections satisfy the group laws. Their cyclic generator
and all its powers retain the prescribed original labels under the common
action, with no faithfulness assumption on the cyclic factor.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
open CyclicCharacteristicAtlas (RelabelGroup)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] (n : ℕ) [NeZero n]
  {T : Scheme} (g : T ⟶ S) (f : Over.mk g ⟶ parameter E n)

/-- The original parameter test over the source of the actual pullback adjunction. -/
def sourcePoint : (Over.map g).obj (𝟙_ (Over T)) ⟶ parameter E n :=
  Over.homMk f.left (by
    change f.left ≫ (parameter E n).hom = 𝟙 T ≫ g
    rw [Category.id_comp]
    exact f.w)

/-- The full original label homomorphism on the actual pulled-back group. -/
def sectionMarking : Label n →* (𝟙_ (Over T) ⟶ (Over.pullback g).obj E) :=
  GroupMarkingBaseChange.marking g E (𝟙_ (Over T))
    (AuxiliaryLevel.markingOf E (Label n) (sourcePoint E n g f))

/-- The homomorphism recovers the previously constructed actual section at every label. -/
theorem sectionMarking_apply (j : Label n) :
    sectionMarking E n g f j = markedSection E n g f j := by
  apply OverPullbackSection.hom_ext
  rw [sectionMarking, GroupMarkingBaseChange.marking_fst, section_fst]
  rfl

/-- The cyclic factor is an actual homomorphism of original group sections. -/
def cyclicMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over T) ⟶ (Over.pullback g).obj E) where
  toFun j := sectionMarking E n g f (1, 1, j)
  map_one' := (sectionMarking E n g f).map_one
  map_mul' x y := by
    simpa only [Prod.mk_mul_mk, _root_.one_mul] using
      (sectionMarking E n g f).map_mul (1, 1, x) (1, 1, y)

/-- The cyclic homomorphism has exactly the original cyclic parameter sections. -/
theorem cyclicMarking_apply (j : Multiplicative (ZMod n)) :
    cyclicMarking E n g f j = markedSection E n g f (1, 1, j) :=
  sectionMarking_apply E n g f (1, 1, j)

/-- Every generator power is the actual original cyclic label. -/
theorem cyclicMarking_generator_pow (r : ℕ) :
    cyclicMarking E n g f (.ofAdd (1 : ZMod n)) ^ r =
      cyclicMarking E n g f (.ofAdd (r : ZMod n)) := by
  simp only [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, _root_.mul_one]

/-- Common relabeling retains the specified cyclic generator powers in the original group. -/
theorem cyclicMarking_action_generator_pow (e : RelabelGroup n) (r : ℕ) :
    cyclicMarking E n g (f ≫ (action E n e).hom) (.ofAdd (1 : ZMod n)) ^ r =
      cyclicMarking E n g f (e.2.2.symm (.ofAdd (r : ZMod n))) := by
  rw [cyclicMarking_generator_pow, cyclicMarking_apply, section_action_cyclic,
    cyclicMarking_apply]

end FLT.Mazur.CyclicBoundaryParameter
