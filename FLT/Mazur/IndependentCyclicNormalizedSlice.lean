/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IndependentCyclicNormalizationParameter
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizationNaturality

/-!
# The closed normalized slice with independent cyclic markings

Forgetting the cyclic factor of the constructed normalized point recovers
exactly the original auxiliary normalization. Hence the full point factors
through the pullback of the original closed normalized slice.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (independentCyclicAuxiliaryScheme n).left)

/-- The actual closed auxiliary slice retaining the entire original cyclic labeling. -/
def independentCyclicNormalizedSlice : Scheme :=
  pullback (independentCyclicAuxiliary n).left normalizedSliceInclusion

/-- Inclusion of the full normalized slice into the original full marking scheme. -/
def independentCyclicNormalizedSliceInclusion :
    independentCyclicNormalizedSlice n ⟶ (independentCyclicAuxiliaryScheme n).left :=
  pullback.fst (independentCyclicAuxiliary n).left normalizedSliceInclusion

/-- The full slice retains the original closed auxiliary slice point. -/
def independentCyclicNormalizedSliceAuxiliary :
    independentCyclicNormalizedSlice n ⟶ normalizedSlice :=
  pullback.snd (independentCyclicAuxiliary n).left normalizedSliceInclusion

/-- The full normalized slice lies over exactly the original auxiliary slice inclusion. -/
@[reassoc] theorem independentCyclicNormalizedSlice_square :
    independentCyclicNormalizedSliceInclusion n ≫ (independentCyclicAuxiliary n).left =
      independentCyclicNormalizedSliceAuxiliary n ≫ normalizedSliceInclusion :=
  pullback.condition

/-- The full slice is a closed subscheme of the actual full marking parameter scheme. -/
instance independentCyclicNormalizedSliceInclusion_isClosedImmersion :
    IsClosedImmersion (independentCyclicNormalizedSliceInclusion n) := by
  dsimp [independentCyclicNormalizedSliceInclusion]
  infer_instance

/-- Every original full cyclic point gives an actual point of the full normalized slice. -/
def independentCyclicNormalizedSlicePoint : T ⟶ independentCyclicNormalizedSlice n :=
  pullback.lift (independentCyclicNormalizedPoint n f)
    (auxiliarySchemeNormalizedSlicePoint (independentCyclicAuxiliaryPoint n f))
    ((independentCyclicNormalizedPoint_auxiliary n f).trans
      (auxiliarySchemeNormalizedSlicePoint_inclusion (independentCyclicAuxiliaryPoint n f)).symm)

/-- The slice lift retains every original normalized full label. -/
@[reassoc] theorem independentCyclicNormalizedSlicePoint_inclusion :
    independentCyclicNormalizedSlicePoint n f ≫ independentCyclicNormalizedSliceInclusion n =
      independentCyclicNormalizedPoint n f :=
  pullback.lift_fst _ _ _

/-- The slice lift retains the original auxiliary normalization as an actual slice point. -/
@[reassoc] theorem independentCyclicNormalizedSlicePoint_auxiliary :
    independentCyclicNormalizedSlicePoint n f ≫ independentCyclicNormalizedSliceAuxiliary n =
      auxiliarySchemeNormalizedSlicePoint (independentCyclicAuxiliaryPoint n f) :=
  pullback.lift_snd _ _ _

/-- Factoring the complete normalized parameter through its closed slice is unique. -/
theorem independentCyclicNormalizedSlicePoint_unique (q : T ⟶ independentCyclicNormalizedSlice n)
    (hq : q ≫ independentCyclicNormalizedSliceInclusion n = independentCyclicNormalizedPoint n f) :
    q = independentCyclicNormalizedSlicePoint n f :=
  (cancel_mono (independentCyclicNormalizedSliceInclusion n)).mp
    (hq.trans (independentCyclicNormalizedSlicePoint_inclusion n f).symm)

end FLT.Mazur.UniversalWeierstrass
