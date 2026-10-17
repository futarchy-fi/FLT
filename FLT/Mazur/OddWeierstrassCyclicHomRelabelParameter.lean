/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomSourceDivisor

/-!
# Odd characteristic chart: independent relabeling of auxiliary and arbitrary cyclic parameters

Both finite label groups act on the actual product parameter scheme over
its unchanged coefficient base. The cyclic factor need not be faithful.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n)))

/-- The auxiliary action as a morphism over its unchanged coefficient base. -/
def cyclicHomAuxiliaryRelabel : levelThree ⟶ levelThree :=
  Over.homMk (levelThreeAction a).hom (levelThreeAction_base a)

/-- Relabel the two factors independently, retaining possible cyclic collisions. -/
def cyclicHomRelabel : cyclicHomAuxiliaryScheme n ⟶ cyclicHomAuxiliaryScheme n :=
  cyclicHomLift n (cyclicHomAuxiliary n ≫ cyclicHomAuxiliaryRelabel a)
    (cyclicHomParameter n ≫ (relabelAction universalGroup c).hom)

/-- Relabeling retains exactly the chosen auxiliary action. -/
@[reassoc] theorem cyclicHomRelabel_auxiliary :
    cyclicHomRelabel n a c ≫ cyclicHomAuxiliary n =
      cyclicHomAuxiliary n ≫ cyclicHomAuxiliaryRelabel a :=
  cyclicHomLift_auxiliary n _ _

/-- Relabeling retains exactly the chosen cyclic action. -/
@[reassoc] theorem cyclicHomRelabel_cyclic :
    cyclicHomRelabel n a c ≫ cyclicHomParameter n =
      cyclicHomParameter n ≫ (relabelAction universalGroup c).hom :=
  cyclicHomLift_cyclic n _ _

/-- The actual cyclic labels follow the inverse convention for the group action. -/
@[reassoc] theorem cyclicHomRelabel_value (i : Multiplicative (ZMod n)) :
    cyclicHomRelabel n a c ≫ cyclicHomParameter n ≫ value universalGroup _ i =
      cyclicHomParameter n ≫ value universalGroup _ (c.symm i) := by
  rw [← Category.assoc, cyclicHomRelabel_cyclic, Category.assoc, relabelAction_value]

/-- Relabeling keeps the original arithmetic coefficient map exactly. -/
@[reassoc] theorem cyclicHomRelabel_base :
    (cyclicHomRelabel n a c).left ≫ (cyclicHomAuxiliaryScheme n).hom =
      (cyclicHomAuxiliaryScheme n).hom := (cyclicHomRelabel n a c).w

/-- Identity labels leave the full original parameter unchanged. -/
theorem cyclicHomRelabel_one : cyclicHomRelabel n 1 1 = 𝟙 _ := by
  apply cyclicHom_hom_ext
  · rw [cyclicHomRelabel_auxiliary, Category.id_comp]
    have h : cyclicHomAuxiliaryRelabel 1 = 𝟙 levelThree := by
      apply Over.OverMorphism.ext
      exact congrArg Iso.hom (map_one (levelThreeAction))
    rw [h, Category.comp_id]
  · rw [cyclicHomRelabel_cyclic, Category.id_comp, map_one]
    exact Category.comp_id _

/-- Composing relabelings gives their actual product action. -/
theorem cyclicHomRelabel_mul (b : MulAut (Labels 3))
    (d : MulAut (Multiplicative (ZMod n))) :
    cyclicHomRelabel n (a * b) (c * d) = cyclicHomRelabel n b d ≫ cyclicHomRelabel n a c := by
  have ha : cyclicHomAuxiliaryRelabel (a * b) =
      cyclicHomAuxiliaryRelabel b ≫ cyclicHomAuxiliaryRelabel a := by
    apply Over.OverMorphism.ext
    exact congrArg Iso.hom (map_mul (levelThreeAction) a b)
  have hc : (relabelAction universalGroup (c * d)).hom =
      (relabelAction universalGroup d).hom ≫ (relabelAction universalGroup c).hom :=
    congrArg Iso.hom (map_mul (relabelAction universalGroup) c d)
  apply cyclicHom_hom_ext
  · rw [cyclicHomRelabel_auxiliary, Category.assoc, cyclicHomRelabel_auxiliary,
      cyclicHomRelabel_auxiliary_assoc, ha]
  · rw [cyclicHomRelabel_cyclic, Category.assoc, cyclicHomRelabel_cyclic,
      cyclicHomRelabel_cyclic_assoc, hc]

end FLT.Mazur.OddWeierstrassParameter
