/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAtlasRelabel
public import FLT.Mazur.AuxiliaryLevelRelabeling

/-!
# Common finite relabeling on actual boundary marking parameters

The homomorphism scheme records commuting auxiliary and cyclic markings in an
arbitrary group scheme. In particular it applies to the split smooth group of
a polygon, including a one-gon. No faithfulness or subgroup rank is imposed:
those are further conditions on the parameters, not consequences of this ambient scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open UniversalWeierstrass (Labels)
open CyclicCharacteristicAtlas (RelabelGroup)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] (n : ℕ) [NeZero n]

/-- The three independent label factors used by the common finite group. -/
abbrev Label := Labels 4 × Labels 3 × Multiplicative (ZMod n)

/-- The actual scheme of homomorphisms from all three label groups. -/
def parameter : Over S := AuxiliaryLevel.homScheme E (Label n)

/-- Componentwise relabeling on the original label group. -/
def labelAction : RelabelGroup n →* MulAut (Label n) where
  toFun e := MulEquiv.prodCongr e.1 (MulEquiv.prodCongr e.2.1 e.2.2)
  map_one' := by ext x <;> rfl
  map_mul' _ _ := by ext x <;> rfl

/-- The same finite group acts on the actual boundary parameter scheme. -/
def action : RelabelGroup n →* Aut (parameter E n) :=
  (AuxiliaryLevel.relabelAction E).comp (labelAction n)

/-- Forgetting the base gives an action on schemes for subsequent quotient constructions. -/
def schemeAction : RelabelGroup n →* Aut (parameter E n).left :=
  (Functor.mapAut (parameter E n) (Over.forget S)).comp (action E n)

/-- Every relabeling preserves the original coefficient morphism exactly. -/
@[reassoc] theorem action_base (e : RelabelGroup n) :
    (schemeAction E n e).hom ≫ (parameter E n).hom = (parameter E n).hom :=
  (action E n e).hom.w

/-- Relabeling uses the inverse convention on each actual marked point. -/
@[reassoc] theorem action_value (e : RelabelGroup n) (j : Label n) :
    (action E n e).hom ≫ AuxiliaryLevel.value E (Label n) j =
      AuxiliaryLevel.value E (Label n) ((labelAction n e).symm j) :=
  AuxiliaryLevel.relabelAction_value E _ j

/-- The cyclic labels move independently of both auxiliary choices. -/
@[reassoc] theorem action_cyclic (e : RelabelGroup n) (j : Multiplicative (ZMod n)) :
    (action E n e).hom ≫ AuxiliaryLevel.value E (Label n) (1, 1, j) =
      AuxiliaryLevel.value E (Label n) (1, 1, e.2.2.symm j) := by
  rw [action_value]
  change AuxiliaryLevel.value E (Label n) (e.1.symm 1, e.2.1.symm 1, e.2.2.symm j) = _
  simp only [map_one]

/-- Level-four labels retain their prescribed original permutation. -/
@[reassoc] theorem action_four (e : RelabelGroup n) (j : Labels 4) :
    (action E n e).hom ≫ AuxiliaryLevel.value E (Label n) (j, 1, 1) =
      AuxiliaryLevel.value E (Label n) (e.1.symm j, 1, 1) := by
  rw [action_value]
  change AuxiliaryLevel.value E (Label n) (e.1.symm j, e.2.1.symm 1, e.2.2.symm 1) = _
  simp only [map_one]

/-- Level-three labels retain their prescribed original permutation. -/
@[reassoc] theorem action_three (e : RelabelGroup n) (j : Labels 3) :
    (action E n e).hom ≫ AuxiliaryLevel.value E (Label n) (1, j, 1) =
      AuxiliaryLevel.value E (Label n) (1, e.2.1.symm j, 1) := by
  rw [action_value]
  change AuxiliaryLevel.value E (Label n) (e.1.symm 1, e.2.1.symm j, e.2.2.symm 1) = _
  simp only [map_one]

end FLT.Mazur.CyclicBoundaryParameter
