/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedIndependentReturn
public import FLT.Mazur.SchemeIndependentEffectivePairReturn

/-!
# Original effective member recovery on base-pair charts

Normalize the proved original recovery equation along the original chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.SchemeCoproductModuleGluing.assembled
attribute [local irreducible] FLT.Mazur.SchemeFppfFamily.IndependentLineData.descended
attribute [local irreducible]
  FLT.Mazur.SchemeFppfFamily.IndependentLineData.descendedMemberRecovery
namespace FLT.Mazur.SchemePicard
open FCurve FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)


/-- Returning the original chart retains the original transition morphism. -/
theorem rigidifiedFamilyIndependentPair_hom_return (i j : 𝒰.I₀) :
    (SchemeIndependentPairNormalization.normalize
    (Limits.pullback.fst ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j))
    (Limits.pullback.snd ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j))
    (relativeCoverPairTotalIso f T 𝒰 i j).hom
    (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))
    (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))
    (relativeCoverPairTotalIso_fst f T 𝒰 i j) (relativeCoverPairTotalIso_snd f T 𝒰 i j)
    ((rigidifiedFamilyIndependentLineData f e he T 𝒰 a ha).obj i).val
    ((rigidifiedFamilyIndependentLineData f e he T 𝒰 a ha).obj j).val
    ((rigidifiedFamilyIndependentLineData f e he T 𝒰 a ha).overlap (i, j))).hom =
    (rigidifiedFamilyPairTransition f e he T 𝒰 a ha i j).val.hom :=
  congrArg (fun q ↦ q.hom) (rigidifiedFamilyIndependentPair_return f e he T 𝒰 a ha i j)


end FLT.Mazur.SchemePicard
