/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicEvenRelabelSections
public import FLT.Mazur.CyclicCharacteristicOddRelabelSections
public import FLT.Mazur.CyclicCharacteristicNormalizedAuxiliary
public import FLT.Mazur.CyclicCharacteristicNormalizedGenerator

/-!
# Common relabeling preserves the specified sections on both actual charts

Both characteristic charts use the same finite relabeling group. Their actual
compatible comparisons retain the corresponding auxiliary permutation and
all prescribed generator powers on every normalized test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open UniversalWeierstrass (Labels)
variable (n : ℕ) [NeZero n]

/-- The auxiliary permutation selected from the common finite relabeling group. -/
def normalizedAuxiliaryRelabel (e : RelabelGroup n) :
    (b : Bool) → MulAut (Labels (normalizedAuxiliaryOrder b))
  | false => e.1
  | true => e.2.1

/-- Common relabeling retains all specified sections on either actual normalized chart. -/
theorem normalizedRelabel_sections {T : Scheme} (b : Bool)
    (v : T ⟶ normalizedLocus n b) (e : RelabelGroup n) :
    ∃ a : CompatibleIso
      ((normalizedSubgroup n b).baseChange (v ≫ (normalizedRelabelAction n b e).hom))
      ((normalizedSubgroup n b).baseChange v),
      (∀ i, pullSection (v ≫ (normalizedRelabelAction n b e).hom)
        (normalizedAuxiliaryMarking n b i) ≫ a.curve.hom.group =
          pullSection v (normalizedAuxiliaryMarking n b
            ((normalizedAuxiliaryRelabel n e b).symm i))) ∧
      ∀ m : ℕ, (pullSection (v ≫ (normalizedRelabelAction n b e).hom)
        (normalizedGenerator n b) ^ m) ≫ a.subgroup.hom =
          pullSection v (normalizedGenerator n b) ^
            (e.2.2.symm (.ofAdd (m : ZMod n))).toAdd.val := by
  cases b
  · exact evenNormalizedRelabel_sections n v e
  · exact oddNormalizedRelabel_sections n v e

end FLT.Mazur.CyclicCharacteristicAtlas
