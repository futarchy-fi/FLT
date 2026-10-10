/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedLocalTrivializations
public import FLT.Mazur.SchemeIndependentEffectiveRecovery
public import FLT.Mazur.SchemeIndependentNormalizationRetraction

/-!
# Original effective recoveries on the original base-pair total spaces

The original pair chart returns the supplied rigidified transition. The
actual effective recoveries intertwine it with canonical global pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] FLT.Mazur.SchemeCoproductModuleGluing.assembled
attribute [local irreducible] FLT.Mazur.SchemeFppfFamily.IndependentLineData.descended
namespace FLT.Mazur.SchemePicard
open FCurve FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)


/-- Returning along the original pair chart recovers the original rigidified transition. -/
theorem rigidifiedFamilyPairIso_return (i j : 𝒰.I₀) :
    SchemeIndependentPairNormalization.normalize
      (Limits.pullback.fst ((relativeTotalCover f T 𝒰).f i)
        ((relativeTotalCover f T 𝒰).f j)) (Limits.pullback.snd _ _)
      (relativeCoverPairTotalIso f T 𝒰 i j).hom
      (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))
      (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))
      (relativeCoverPairTotalIso_fst f T 𝒰 i j)
      (relativeCoverPairTotalIso_snd f T 𝒰 i j) _ _
      (rigidifiedFamilyPairIso f e he T 𝒰 a ha i j) =
        (rigidifiedFamilyPairTransition f e he T 𝒰 a ha i j).val :=
  SchemeIndependentPairNormalization.normalize_retract _ _ _ _
    (relativeCoverPairTotalIso f T 𝒰 i j).hom_inv_id _ _ _ _ _ _ _ _ _

/-- Canonical overlap of the effective global line on the original pair total space. -/
def rigidifiedFamilyEffectivePair (i j : 𝒰.I₀) :=
  SchemeIndependentCanonicalOverlap.overlap
    ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
    (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))
    (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))
    (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫ (relativeTotalCover f T 𝒰).f i)
    rfl (by
      change relativeTotalMap f (relativeCoverPairRight T 𝒰 i j) ≫
          relativeTotalMap f (relativeCoverArrow T 𝒰 j) =
        relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫
          relativeTotalMap f (relativeCoverArrow T 𝒰 i)
      rw [← relativeTotalMap_comp, ← relativeTotalMap_comp, relativeCoverPair_condition])
    (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha).val

end FLT.Mazur.SchemePicard
