/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedIndependentHomReturn
public import FLT.Mazur.ProperFamilyRigidifiedEffectiveRecoveryCharts
public import FLT.Mazur.SchemeIndependentEffectivePairReturn

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

/-- The original datum has its effective recovery equation on each original pair chart. -/
theorem rigidifiedFamilyRecovery_returnedChart (i j : 𝒰.I₀)
    (hr : relativeTotalMap f (relativeCoverPairRight T 𝒰 i j) ≫
      (relativeTotalCover f T 𝒰).f j =
      relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫
        (relativeTotalCover f T 𝒰).f i) :
    let D := rigidifiedFamilyIndependentLineData f e he T 𝒰 a ha
    (SchemeIndependentCanonicalOverlap.overlap
      ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
      (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))
      (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))
      (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫ (relativeTotalCover f T 𝒰).f i)
      rfl hr D.descended.val).hom ≫
      (Scheme.Modules.pullback (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))).map
        (D.descendedMemberRecovery j).hom =
    (Scheme.Modules.pullback (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))).map
      (D.descendedMemberRecovery i).hom ≫
      (rigidifiedFamilyPairTransition f e he T 𝒰 a ha i j).val.hom := by
  have h := rigidifiedFamilyRecovery_chart f e he T 𝒰 a ha i j hr
  have hret := rigidifiedFamilyIndependentPair_hom_return f e he T 𝒰 a ha i j
  have hmul := congrArg (fun m ↦
    (Scheme.Modules.pullback (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))).map
      ((rigidifiedFamilyIndependentLineData f e he T 𝒰 a ha).descendedMemberRecovery i).hom ≫ m)
    hret
  exact h.trans hmul

end FLT.Mazur.SchemePicard
