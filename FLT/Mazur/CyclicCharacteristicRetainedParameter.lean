/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicRetainedFaithfulness
public import FLT.Mazur.AuxiliaryDistinctSectionParameter

/-!
# Faithful scheme parameters for the retained original auxiliary frames

The actual normalized chart comparison constructs a map into the faithful
marking open of the original group. Evaluating it gives every original label,
so this factorization does not replace the frame by a separately chosen one.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open AuxiliaryLevel
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Both characteristic choices have positive auxiliary order. -/
instance normalizedAuxiliaryOrder_neZero (b : Bool) : NeZero (normalizedAuxiliaryOrder b) :=
  ⟨by cases b <;> decide⟩

variable {S : Scheme} {E : GeneralizedEllipticCurve S}

/-- The retained parameter uses the separation inherited from the original proper curve. -/
local instance retainedParameterGroupSeparated : IsSeparated E.group.hom := by
  let _ : IsProper E.curve.hom := E.family.family.1
  rw [← E.inclusion.w]
  infer_instance

variable {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) (b : Bool)
  (q : S ⟶ normalizedLocus n b)
  (a : CompatibleIso ((normalizedSubgroup n b).baseChange q) H)
  (m : Labels (normalizedAuxiliaryOrder b) →* (𝟙_ (Over S) ⟶ E.group))
  (hm : ∀ i, pullSection q (normalizedAuxiliaryMarking n b i) ≫ a.curve.hom.group = m i)

/-- The retained original frame as an actual point of its faithful marking open. -/
def retainedAuxiliaryParameter :
    𝟙_ (Over S) ⟶ faithfulScheme E.group (Labels (normalizedAuxiliaryOrder b)) :=
  distinctSectionParameter E.group _ m (retainedAuxiliary_distinct H b q a m hm)

/-- Forgetting the faithful open recovers the equation point of the original frame. -/
theorem retainedAuxiliaryParameter_inclusion :
    retainedAuxiliaryParameter H b q a m hm ≫ faithfulInclusion E.group _ =
      liftMarking E.group _ m := by
  rw [retainedAuxiliaryParameter, distinctSectionParameter, faithfulLift_inclusion]

/-- Every evaluation recovers its specified original section exactly. -/
@[reassoc] theorem retainedAuxiliaryParameter_value (i : Labels (normalizedAuxiliaryOrder b)) :
    retainedAuxiliaryParameter H b q a m hm ≫ faithfulInclusion E.group _ ≫
      value E.group _ i = m i :=
  distinctSectionParameter_value E.group _ m (retainedAuxiliary_distinct H b q a m hm) i

end FLT.Mazur.CyclicCharacteristicAtlas
