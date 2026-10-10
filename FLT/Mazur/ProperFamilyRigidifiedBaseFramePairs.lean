/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedEffectivePair
public import FLT.Mazur.SchemeSectionFrameCompatibility

/-!
# Agreement of the original descended section frames on base pairs

Use the actual recovery and transition preservation equations through the
original section squares. The specified local frames agree on original overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  (T : Over S) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)
  (a : ∀ i, RigidifiedPic (pointedBaseSection f e he (relativeCoverMember T 𝒰 i)))
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]
  (ha : RigidifiedFamilyMatching f e he T 𝒰 a)


/-- The specified base trivializations agree on each original base-pair overlap. -/
theorem rigidifiedFamilyBaseTrivialization_pair (i j : 𝒰.I₀) :
    (SchemeIndependentCanonicalOverlap.pair (𝒰.f i) (𝒰.f j)
        ((Scheme.Modules.pullback (pointedBaseSection f e he T)).obj
          (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha).val)).hom ≫
      (Scheme.Modules.pullback (Limits.pullback.snd (𝒰.f i) (𝒰.f j))).map
        (rigidifiedFamilyBaseTrivialization f e he T 𝒰 a ha j).hom ≫
      (modulePullbackUnitIso (Limits.pullback.snd (𝒰.f i) (𝒰.f j))).hom =
    (Scheme.Modules.pullback (Limits.pullback.fst (𝒰.f i) (𝒰.f j))).map
        (rigidifiedFamilyBaseTrivialization f e he T 𝒰 a ha i).hom ≫
      (modulePullbackUnitIso (Limits.pullback.fst (𝒰.f i) (𝒰.f j))).hom := by
  have hr : relativeTotalMap f (relativeCoverPairRight T 𝒰 i j) ≫
      (relativeTotalCover f T 𝒰).f j =
      relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫
        (relativeTotalCover f T 𝒰).f i := by
    change relativeTotalMap f (relativeCoverPairRight T 𝒰 i j) ≫
        relativeTotalMap f (relativeCoverArrow T 𝒰 j) =
      relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫
        relativeTotalMap f (relativeCoverArrow T 𝒰 i)
    rw [← relativeTotalMap_comp, ← relativeTotalMap_comp, relativeCoverPair_condition]
  have hp := rigidifiedFamilyEffectivePair_preserves f e he T 𝒰 a ha i j
  dsimp only [rigidifiedBasePullback, rigidifiedBundlePullback, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom] at hp
  have h := SchemePullbackSquare.sectionFrames_pair
    (U := Limits.pullback (𝒰.f i) (𝒰.f j))
    (pointedBaseSection f e he T)
    (pointedBaseSection f e he (relativeCoverMember T 𝒰 i))
    (pointedBaseSection f e he (relativeCoverMember T 𝒰 j))
    (pointedBaseSection f e he (relativeCoverPair T 𝒰 i j))
    (relativeTotalMap f (relativeCoverArrow T 𝒰 i))
    (relativeTotalMap f (relativeCoverArrow T 𝒰 j)) (𝒰.f i) (𝒰.f j)
    (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j))
    (relativeTotalMap f (relativeCoverPairRight T 𝒰 i j))
    (Limits.pullback.fst (𝒰.f i) (𝒰.f j)) (Limits.pullback.snd (𝒰.f i) (𝒰.f j))
    (pointedBaseSection_naturality f e he (relativeCoverArrow T 𝒰 i))
    (pointedBaseSection_naturality f e he (relativeCoverArrow T 𝒰 j))
    (pointedBaseSection_naturality f e he (relativeCoverPairLeft T 𝒰 i j))
    (pointedBaseSection_naturality f e he (relativeCoverPairRight T 𝒰 i j))
    (relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) ≫ (relativeTotalCover f T 𝒰).f i)
    (Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
    rfl hr rfl Limits.pullback.condition.symm
    (rigidifiedFamilyDescendedLine f e he T 𝒰 a ha).val
    (rigidifiedFamilyRestrictedBundle f e he T 𝒰 a ha i).2
    (rigidifiedFamilyRestrictedBundle f e he T 𝒰 a ha j).2 hp
  simpa only [rigidifiedFamilyBaseTrivialization, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, SchemeIndependentCanonicalOverlap.pair] using h

end FLT.Mazur.SchemePicard
