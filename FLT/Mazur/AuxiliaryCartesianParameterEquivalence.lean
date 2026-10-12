/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryCartesianOriginalParameter

/-!
# Cartesian faithful parameters form a natural equivalence

Returning a realized full marking to its original base commutes with every
change of test scheme. The two constructions are inverse on actual parameters.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme} (g : T ⟶ S) (G : CommGrp (Over S)) (H : CommGrp (Over T))
  [IsSeparated G.X.hom] [IsSeparated H.X.hom]
  (e : (Over.pullback g).mapCommGrp.obj G ≅ H) (A : Type) [Group A] [Fintype A]

/-- Returning complete faithful parameters commutes with every test-scheme map. -/
@[reassoc] theorem originalGroupParameter_natural {U V : Over T}
    (f : U ⟶ faithfulScheme H.X A) (k : V ⟶ U) :
    (Over.map g).map k ≫ originalGroupParameter g G H e A f =
      originalGroupParameter g G H e A (k ≫ f) := by
  apply faithfulParameter_ext G A
  intro a
  rw [Category.assoc, originalGroupParameter_value, originalGroupParameter_value]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, originalGroupMarking_left, Category.assoc]
  rfl

/-- Returning and then realizing a faithful parameter restores the original parameter. -/
theorem cartesianGroupParameter_original {U : Over T} (f : U ⟶ faithfulScheme H.X A) :
    cartesianGroupParameter g G H e A (originalGroupParameter g G H e A f) = f := by
  apply faithfulParameter_ext H A
  intro a
  rw [cartesianGroupParameter_value]
  apply GroupMarkingCartesianTransport.point_ext g G H e U
  rw [cartesianGroupMarking_projection]
  rw [originalGroupParameter_value, originalGroupMarking_left]

/-- Realizing and then returning a faithful parameter restores all original labels. -/
theorem originalGroupParameter_cartesian {U : Over T}
    (f : (Over.map g).obj U ⟶ faithfulScheme G.X A) :
    originalGroupParameter g G H e A (cartesianGroupParameter g G H e A f) = f := by
  apply faithfulParameter_ext G A
  intro a
  rw [originalGroupParameter_value]
  apply Over.OverMorphism.ext
  rw [originalGroupMarking_left, cartesianGroupParameter_value,
    cartesianGroupMarking_projection]

/-- Actual faithful parameters are equivalent across the chosen cartesian realization. -/
def cartesianParameterEquiv (U : Over T) :
    ((Over.map g).obj U ⟶ faithfulScheme G.X A) ≃ (U ⟶ faithfulScheme H.X A) where
  toFun := cartesianGroupParameter g G H e A
  invFun := originalGroupParameter g G H e A
  left_inv := originalGroupParameter_cartesian g G H e A
  right_inv := cartesianGroupParameter_original g G H e A

end FLT.Mazur.AuxiliaryLevel
