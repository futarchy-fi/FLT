/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupTorsionCommutativeStructure
public import FLT.Mazur.EtaleMarkingScheme

/-!
# Marking equations factor through the full torsion group

If n kills the label group, marking the original group is equivalent to
marking its actual n-torsion equalizer. This is an isomorphism of the equation
schemes, not just of their geometric points. Etaleness of torsion therefore
proves etaleness of the original faithful-marking scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.AuxiliaryTorsionMarkingComparison

open AuxiliaryLevel

variable {S : Scheme} (E : Over S) [CommGrpObj E] (n : ℕ)
  (A : Type) [Group A] [Fintype A] (hA : ∀ a : A, a ^ n = 1)

include hA in
/-- Every value of the original universal marking is killed by the label exponent. -/
theorem value_pow (a : A) : universalMarking E A a ^ n = 1 := by
  rw [← map_pow, hA, map_one]

/-- The universal original marking determines a marking of the full torsion equalizer. -/
def toTorsion : homScheme E A ⟶ homScheme (GroupTorsionScheme.scheme E n) A :=
  liftMarking _ A (GroupTorsionScheme.liftMarking E n (universalMarking E A)
    (value_pow E n A hA))

/-- A torsion-valued marking gives an original group-valued marking by inclusion. -/
def fromTorsion : homScheme (GroupTorsionScheme.scheme E n) A ⟶ homScheme E A :=
  liftMarking E A ((IsMonHom.monoidHom (GroupTorsionScheme.inclusion E n) _).comp
    (universalMarking (GroupTorsionScheme.scheme E n) A))

/-- The forward comparison preserves the original values. -/
@[reassoc (attr := simp)] theorem toTorsion_value (a : A) :
    toTorsion E n A hA ≫ value (GroupTorsionScheme.scheme E n) A a ≫
      GroupTorsionScheme.inclusion E n = value E A a := by
  rw [← Category.assoc, toTorsion, liftMarking_value, GroupTorsionScheme.liftMarking_inclusion]
  rfl

/-- The reverse comparison is the actual inclusion on every marked value. -/
@[reassoc (attr := simp)] theorem fromTorsion_value (a : A) :
    fromTorsion E n A ≫ value E A a =
      value (GroupTorsionScheme.scheme E n) A a ≫ GroupTorsionScheme.inclusion E n :=
  liftMarking_value _ _ _ _

/-- The original marking equation scheme is isomorphic to the torsion marking equation scheme. -/
def iso : homScheme E A ≅ homScheme (GroupTorsionScheme.scheme E n) A where
  hom := toTorsion E n A hA
  inv := fromTorsion E n A
  hom_inv_id := by
    apply homScheme_ext
    intro a
    simp only [Category.assoc, fromTorsion_value, toTorsion_value, Category.id_comp]
  inv_hom_id := by
    apply homScheme_ext
    intro a
    apply (cancel_mono (GroupTorsionScheme.inclusion E n)).mp
    simp only [Category.assoc, toTorsion_value, fromTorsion_value, Category.id_comp]

include hA in
/-- Etaleness of full torsion implies etaleness of the original marking equation scheme. -/
theorem homScheme_etale [Etale (GroupTorsionScheme.scheme E n).hom] :
    Etale (homScheme E A).hom := by
  have := EtaleMarkingScheme.homScheme_etale (GroupTorsionScheme.scheme E n) A
  have : Etale ((iso E n A hA).hom.left ≫ (homScheme (GroupTorsionScheme.scheme E n) A).hom) :=
    inferInstance
  rwa [(iso E n A hA).hom.w] at this

include hA in
/-- The original universally faithful marking scheme is etale whenever full torsion is etale. -/
theorem faithfulScheme_etale [IsSeparated E.hom]
    [Etale (GroupTorsionScheme.scheme E n).hom] : Etale (faithfulScheme E A).hom := by
  have := homScheme_etale E n A hA
  change Etale ((faithfulOpen E A).ι ≫ (homScheme E A).hom)
  infer_instance

end FLT.Mazur.AuxiliaryTorsionMarkingComparison
