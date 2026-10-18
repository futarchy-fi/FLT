/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryParameterAction
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Independent original markings give actual boundary parameters

For a commutative group scheme, any original auxiliary and cyclic markings
produce a test of the constructed parameter scheme. All three original
markings are recovered exactly, and the construction commutes with the
common finite relabeling action. No frame is chosen using a desired comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open UniversalWeierstrass (Labels)
open CyclicCharacteristicAtlas (RelabelGroup)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] [IsCommMonObj E]
  (n : ℕ) [NeZero n] {U : Over S}
  (a : Labels 4 →* (U ⟶ E)) (b : Labels 3 →* (U ⟶ E))
  (c : Multiplicative (ZMod n) →* (U ⟶ E))

/-- Combine the original independent markings in their unchanged commutative group. -/
def combinedMarking : Label n →* (U ⟶ E) where
  toFun j := a j.1 * b j.2.1 * c j.2.2
  map_one' := by
    change a 1 * b 1 * c 1 = 1
    simp only [map_one, _root_.mul_one]
  map_mul' x y := by
    change a (x.1 * y.1) * b (x.2.1 * y.2.1) * c (x.2.2 * y.2.2) = _
    simp only [map_mul]
    ac_rfl

/-- The actual boundary test determined by three original independent markings. -/
def ofMarkings : U ⟶ parameter E n :=
  AuxiliaryLevel.liftMarking E (Label n) (combinedMarking E n a b c)

/-- Every universal label has its original group value on the constructed test. -/
@[reassoc] theorem ofMarkings_value (j : Label n) :
    ofMarkings E n a b c ≫ AuxiliaryLevel.value E (Label n) j =
      a j.1 * b j.2.1 * c j.2.2 :=
  AuxiliaryLevel.liftMarking_value _ _ _ _

/-- The actual test recovers the independent level-four marking exactly. -/
@[reassoc] theorem ofMarkings_four (j : Labels 4) :
    ofMarkings E n a b c ≫ AuxiliaryLevel.value E (Label n) (j, 1, 1) = a j := by
  rw [ofMarkings_value, map_one, map_one, _root_.mul_one, _root_.mul_one]

/-- The actual test recovers the independent level-three marking exactly. -/
@[reassoc] theorem ofMarkings_three (j : Labels 3) :
    ofMarkings E n a b c ≫ AuxiliaryLevel.value E (Label n) (1, j, 1) = b j := by
  rw [ofMarkings_value, map_one, map_one, _root_.one_mul, _root_.mul_one]

/-- The actual test recovers every original cyclic label, including coincident ones. -/
@[reassoc] theorem ofMarkings_cyclic (j : Multiplicative (ZMod n)) :
    ofMarkings E n a b c ≫ AuxiliaryLevel.value E (Label n) (1, 1, j) = c j := by
  rw [ofMarkings_value, map_one, map_one, _root_.one_mul, _root_.one_mul]

/-- Relabeling the original input agrees with the actual finite action on its parameter test. -/
theorem ofMarkings_action (e : RelabelGroup n) :
    ofMarkings E n a b c ≫ (action E n e).hom =
      ofMarkings E n (a.comp e.1.symm.toMonoidHom)
        (b.comp e.2.1.symm.toMonoidHom) (c.comp e.2.2.symm.toMonoidHom) := by
  apply AuxiliaryLevel.homScheme_ext
  intro j
  rw [Category.assoc, action_value, ofMarkings_value, ofMarkings_value]
  rfl

end FLT.Mazur.CyclicBoundaryParameter
