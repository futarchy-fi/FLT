/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationIdempotence

/-!
# The actual normalized slice with the full cyclic marking

Forgetting the cyclic factor of the constructed normalized point recovers
exactly the original auxiliary normalization. Hence the full point factors
through the pullback of the original closed normalized slice.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)

/-- The actual closed auxiliary slice retaining the entire original cyclic labeling. -/
def cyclicHomNormalizedSlice : Scheme :=
  pullback (cyclicHomAuxiliary n).left normalizedSliceInclusion

/-- Inclusion of the full normalized slice into the original full marking scheme. -/
def cyclicHomNormalizedSliceInclusion :
    cyclicHomNormalizedSlice n ⟶ (cyclicHomAuxiliaryScheme n).left :=
  pullback.fst (cyclicHomAuxiliary n).left normalizedSliceInclusion

/-- The full slice retains the original closed auxiliary slice point. -/
def cyclicHomNormalizedSliceAuxiliary : cyclicHomNormalizedSlice n ⟶ normalizedSlice :=
  pullback.snd (cyclicHomAuxiliary n).left normalizedSliceInclusion

/-- The full normalized slice lies over exactly the original auxiliary slice inclusion. -/
@[reassoc] theorem cyclicHomNormalizedSlice_square :
    cyclicHomNormalizedSliceInclusion n ≫ (cyclicHomAuxiliary n).left =
      cyclicHomNormalizedSliceAuxiliary n ≫ normalizedSliceInclusion :=
  pullback.condition

/-- The full slice is a closed subscheme of the actual full marking parameter scheme. -/
instance cyclicHomNormalizedSliceInclusion_isClosedImmersion :
    IsClosedImmersion (cyclicHomNormalizedSliceInclusion n) := by
  dsimp [cyclicHomNormalizedSliceInclusion]
  infer_instance

/-- Every original full cyclic point gives an actual point of the full normalized slice. -/
def cyclicHomNormalizedSlicePoint : T ⟶ cyclicHomNormalizedSlice n :=
  pullback.lift (cyclicHomNormalizedPoint n f)
    (auxiliarySchemeNormalizedSlicePoint (cyclicHomAuxiliaryPoint n f))
    ((cyclicHomNormalizedPoint_auxiliary n f).trans
      (auxiliarySchemeNormalizedSlicePoint_inclusion (cyclicHomAuxiliaryPoint n f)).symm)

/-- The slice lift retains every original normalized full label. -/
@[reassoc] theorem cyclicHomNormalizedSlicePoint_inclusion :
    cyclicHomNormalizedSlicePoint n f ≫ cyclicHomNormalizedSliceInclusion n =
      cyclicHomNormalizedPoint n f :=
  pullback.lift_fst _ _ _

/-- The slice lift retains the original auxiliary normalization as an actual slice point. -/
@[reassoc] theorem cyclicHomNormalizedSlicePoint_auxiliary :
    cyclicHomNormalizedSlicePoint n f ≫ cyclicHomNormalizedSliceAuxiliary n =
      auxiliarySchemeNormalizedSlicePoint (cyclicHomAuxiliaryPoint n f) :=
  pullback.lift_snd _ _ _

/-- Factoring the complete normalized parameter through its closed slice is unique. -/
theorem cyclicHomNormalizedSlicePoint_unique (q : T ⟶ cyclicHomNormalizedSlice n)
    (hq : q ≫ cyclicHomNormalizedSliceInclusion n = cyclicHomNormalizedPoint n f) :
    q = cyclicHomNormalizedSlicePoint n f :=
  (cancel_mono (cyclicHomNormalizedSliceInclusion n)).mp
    (hq.trans (cyclicHomNormalizedSlicePoint_inclusion n f).symm)

end FLT.Mazur.OddWeierstrassParameter
