/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicNormalizedMarking
public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeNormalizationNaturality

/-!
# The actual normalized slice with the full cyclic marking

Forgetting the cyclic factor of the constructed normalized point recovers
exactly the original auxiliary normalization. Hence the full point factors
through the pullback of the original closed normalized slice.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicAuxiliaryScheme n).left)

/-- Full cyclic normalization retains exactly the independently constructed auxiliary point. -/
@[reassoc] theorem cyclicSchemeNormalizedPoint_forget :
    cyclicSchemeNormalizedPoint n f ≫ (forgetCyclic n).left =
      auxiliarySchemeNormalizedPoint (cyclicSchemeAuxiliaryPoint n f) := by
  apply auxiliarySchemePoint_ext
  · rw [Category.assoc, (forgetCyclic n).w, cyclicSchemeNormalizedPoint_base]
  · intro c
    rw [Category.assoc, forgetCyclic_value, ← cyclicSchemeNormalizedMarking_fst,
      cyclicSchemeNormalizedMarking_auxiliary, auxiliarySchemeMarking_fst]

/-- The actual closed auxiliary slice retaining the entire original cyclic labeling. -/
def cyclicNormalizedSlice : Scheme :=
  pullback (forgetCyclic n).left normalizedSliceInclusion

/-- Inclusion of the full normalized slice into the original full marking scheme. -/
def cyclicNormalizedSliceInclusion : cyclicNormalizedSlice n ⟶ (cyclicAuxiliaryScheme n).left :=
  pullback.fst (forgetCyclic n).left normalizedSliceInclusion

/-- The full slice retains the original closed auxiliary slice point. -/
def cyclicNormalizedSliceAuxiliary : cyclicNormalizedSlice n ⟶ normalizedSlice :=
  pullback.snd (forgetCyclic n).left normalizedSliceInclusion

/-- The full normalized slice lies over exactly the original auxiliary slice inclusion. -/
@[reassoc] theorem cyclicNormalizedSlice_square :
    cyclicNormalizedSliceInclusion n ≫ (forgetCyclic n).left =
      cyclicNormalizedSliceAuxiliary n ≫ normalizedSliceInclusion :=
  pullback.condition

/-- The full slice is a closed subscheme of the actual full marking parameter scheme. -/
instance cyclicNormalizedSliceInclusion_isClosedImmersion :
    IsClosedImmersion (cyclicNormalizedSliceInclusion n) := by
  dsimp [cyclicNormalizedSliceInclusion]
  infer_instance

/-- Every original full cyclic point gives an actual point of the full normalized slice. -/
def cyclicSchemeNormalizedSlicePoint : T ⟶ cyclicNormalizedSlice n :=
  pullback.lift (cyclicSchemeNormalizedPoint n f)
    (auxiliarySchemeNormalizedSlicePoint (cyclicSchemeAuxiliaryPoint n f))
    ((cyclicSchemeNormalizedPoint_forget n f).trans
      (auxiliarySchemeNormalizedSlicePoint_inclusion (cyclicSchemeAuxiliaryPoint n f)).symm)

/-- The slice lift retains every original normalized full label. -/
@[reassoc] theorem cyclicSchemeNormalizedSlicePoint_inclusion :
    cyclicSchemeNormalizedSlicePoint n f ≫ cyclicNormalizedSliceInclusion n =
      cyclicSchemeNormalizedPoint n f :=
  pullback.lift_fst _ _ _

/-- The slice lift retains the original auxiliary normalization as an actual slice point. -/
@[reassoc] theorem cyclicSchemeNormalizedSlicePoint_auxiliary :
    cyclicSchemeNormalizedSlicePoint n f ≫ cyclicNormalizedSliceAuxiliary n =
      auxiliarySchemeNormalizedSlicePoint (cyclicSchemeAuxiliaryPoint n f) :=
  pullback.lift_snd _ _ _

/-- Factoring the complete normalized parameter through its closed slice is unique. -/
theorem cyclicSchemeNormalizedSlicePoint_unique (q : T ⟶ cyclicNormalizedSlice n)
    (hq : q ≫ cyclicNormalizedSliceInclusion n = cyclicSchemeNormalizedPoint n f) :
    q = cyclicSchemeNormalizedSlicePoint n f :=
  (cancel_mono (cyclicNormalizedSliceInclusion n)).mp
    (hq.trans (cyclicSchemeNormalizedSlicePoint_inclusion n f).symm)

end FLT.Mazur.UniversalWeierstrass
