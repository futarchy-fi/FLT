/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedReturnedRecoveryCharts

/-!
# Original effective member recovery on base-pair charts

Normalize the proved original recovery equation along the original chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.SchemeCoproductModuleGluing.assembled
attribute [local irreducible] FLT.Mazur.SchemeFppfFamily.IndependentLineData.descended
attribute [local irreducible]
  FLT.Mazur.SchemeFppfFamily.IndependentLineData.descendedMemberRecovery
attribute [local irreducible] Scheme.Modules.pullback SheafOfModules.pullback
namespace FLT.Mazur.SchemePicard
open FCurve FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)


attribute [local irreducible] rigidifiedFamilyRepresentative rigidifiedFamilyPairTransition
attribute [local irreducible] relativeTotalMap

/-- The original recovery wrapper is exactly the original datum recovery. -/
theorem rigidifiedFamilyDescendedMember_eq_recovery (i : 𝒰.I₀) :
    rigidifiedFamilyDescendedMember f e he T 𝒰 a ha i =
      (rigidifiedFamilyIndependentLineData f e he T 𝒰 a ha).descendedMemberRecovery i := rfl

/-- The original effective pair has exactly the native canonical overlap. -/
theorem rigidifiedFamilyEffectivePair_eq_overlap (i j : 𝒰.I₀)
    (hr : relativeTotalMap f (relativeCoverPairRight T 𝒰 i j) ≫
      (relativeTotalCover f T 𝒰).f j =
      relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫
        (relativeTotalCover f T 𝒰).f i) :
    rigidifiedFamilyEffectivePair f e he T 𝒰 a ha i j =
      SchemeIndependentCanonicalOverlap.overlap
        ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))
        (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))
        (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫ (relativeTotalCover f T 𝒰).f i)
        rfl hr (rigidifiedFamilyIndependentLineData f e he T 𝒰 a ha).descended.val := rfl


/-- The original effective recoveries intertwine the original rigidified transition. -/
theorem rigidifiedFamilyDescendedMember_pair (i j : 𝒰.I₀) :
    (rigidifiedFamilyEffectivePair f e he T 𝒰 a ha i j).hom ≫
      (Scheme.Modules.pullback (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))).map
        (rigidifiedFamilyDescendedMember f e he T 𝒰 a ha j).hom =
    (Scheme.Modules.pullback (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))).map
        (rigidifiedFamilyDescendedMember f e he T 𝒰 a ha i).hom ≫
      (rigidifiedFamilyPairTransition f e he T 𝒰 a ha i j).val.hom := by
  have hr : relativeTotalMap f (relativeCoverPairRight T 𝒰 i j) ≫
      (relativeTotalCover f T 𝒰).f j =
      relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫
        (relativeTotalCover f T 𝒰).f i := by
    change relativeTotalMap f (relativeCoverPairRight T 𝒰 i j) ≫
        relativeTotalMap f (relativeCoverArrow T 𝒰 j) =
      relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫
        relativeTotalMap f (relativeCoverArrow T 𝒰 i)
    rw [← relativeTotalMap_comp, ← relativeTotalMap_comp, relativeCoverPair_condition]
  simp only [rigidifiedFamilyEffectivePair_eq_overlap f e he T 𝒰 a ha i j hr,
    rigidifiedFamilyDescendedMember_eq_recovery]
  exact rigidifiedFamilyRecovery_returnedChart f e he T 𝒰 a ha i j hr

end FLT.Mazur.SchemePicard
