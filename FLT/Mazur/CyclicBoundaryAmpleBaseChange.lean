/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryBaseChangeAmpleCriterion

/-!
# The actual ample boundary scheme commutes with base change

The ample open is exactly the inverse image of the original ample open. Its
constructed projection is cartesian both over faithful parameters and over the
original base, so the comparison applies to arbitrary singular families.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : GeneralizedEllipticCurve S)
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
  (n : ℕ) [NeZero n]

local instance ampleComparisonPullbackGroup_separated :
    IsSeparated (E.baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom g))

local instance ampleComparisonPullbackGroup_smooth :
    SmoothOfRelativeDimension 1 (E.baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom g
    inferInstance

local notation "q" => faithfulBaseChangeToOriginal g E.group n
local notation "I" => ampleParameterOpen E n
local notation "J" => ampleParameterOpen (E.baseChange g) n

/-- The ample open is the exact inverse image under the faithful parameter comparison. -/
theorem ampleParameterOpen_baseChange : (J) = (q) ⁻¹ᵁ (I) := by
  apply le_antisymm
  · intro x hx
    have hr := (ampleParameter_baseChange_criterion g E n (J).ι).mp (by
      rintro _ ⟨y, rfl⟩
      exact y.property)
    exact hr ⟨⟨x, hx⟩, rfl⟩
  · intro x hx
    have hr := (ampleParameter_baseChange_criterion g E n ((q) ⁻¹ᵁ (I)).ι).mpr (by
      rintro _ ⟨y, rfl⟩
      exact y.property)
    exact hr ⟨⟨x, hx⟩, rfl⟩

/-- The ample restriction is the actual pullback of the original open immersion. -/
theorem ampleBaseChangeToOriginal_open_isPullback :
    IsPullback (ampleBaseChangeToOriginal g E n) (J).ι (I).ι (q) := by
  apply IsOpenImmersion.isPullback
  · exact (ampleBaseChangeToOriginal_inclusion g E n).symm
  · simpa only [Scheme.Opens.opensRange_ι] using
      (ampleParameterOpen_baseChange g E n).symm

/-- The structure morphism of the actual ample boundary parameter. -/
def ampleParameterBase : ampleParameter E n ⟶ S :=
  (I).ι ≫ (cyclicFaithfulParameter E.group n).hom

/-- The ample parameter comparison is cartesian over the original arbitrary base morphism. -/
theorem ampleBaseChangeToOriginal_isPullback :
    IsPullback (ampleBaseChangeToOriginal g E n) (ampleParameterBase (E.baseChange g) n)
      (ampleParameterBase E n) g :=
  (ampleBaseChangeToOriginal_open_isPullback g E n).paste_vert
    (faithfulBaseChangeToOriginal_isPullback g E.group n)

/-- The actual pulled-back ample scheme is isomorphic to the new ample parameter scheme. -/
def ampleBaseChangeIso :
    pullback (ampleParameterBase E n) g ≅ ampleParameter (E.baseChange g) n :=
  (ampleBaseChangeToOriginal_isPullback g E n).isoPullback.symm

/-- The scheme comparison retains its original ample parameter exactly. -/
@[reassoc] theorem ampleBaseChangeIso_hom_original :
    (ampleBaseChangeIso g E n).hom ≫ ampleBaseChangeToOriginal g E n =
      pullback.fst (ampleParameterBase E n) g :=
  (ampleBaseChangeToOriginal_isPullback g E n).isoPullback_inv_fst

/-- The scheme comparison retains its new base exactly. -/
@[reassoc] theorem ampleBaseChangeIso_hom_base :
    (ampleBaseChangeIso g E n).hom ≫ ampleParameterBase (E.baseChange g) n =
      pullback.snd (ampleParameterBase E n) g :=
  (ampleBaseChangeToOriginal_isPullback g E n).isoPullback_inv_snd

end FLT.Mazur.CyclicBoundaryParameter
