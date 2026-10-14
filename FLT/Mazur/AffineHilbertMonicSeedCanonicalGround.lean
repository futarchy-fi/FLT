/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGroundRelativeCoverage
public import FLT.Mazur.AffineHilbertMonicSeedArbitraryGround

/-!
# Canonical ground changes preserve the entire selected seed quotient

Choose the new translation to be the actual ground pullback of the old one.
Its relative comparison is the identity, so the image and coverage results
have no translation-surjectivity premise. The resulting joint effective
scheme is isomorphic to the full pulled-back SELECTED old coefficient image.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The canonical relative translation comparison is literally the identity. -/
theorem RelativeCoefficientBaseChange.canonical_projection
    {S S' : Scheme} (a : S' ⟶ S) (V : Over S) :
    projection a (toOld a (T := V)) (𝟙 V) = 𝟙 (target a (T := V)) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [projection, toOld, Over.homMk_left, Over.id_left,
      Category.comp_id, Category.id_comp, pullback.lift_fst]
  · simp only [projection, Over.homMk_left, Over.id_left,
      target, Over.pullback_obj_hom, Category.id_comp, pullback.lift_snd]

namespace HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {Z : Scheme} (s : Z ⟶ A.left) [Etale s]
  [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)]
  (z : (pullback (snd f hL d V c k).left s : Scheme))
local notation "W" => RelativeCoefficientBaseChange.target a (T := V)
local notation "t" => RelativeCoefficientBaseChange.toOld a (T := V)
local notation "v" => monicSeedAffineMap f hL d V c k s z
local notation "k₀" => monicSeedAffineChart f hL d V c k s z
local notation "w₀" => finiteKernelProjection f hL d V c k
local notation "u" => monicSeedGroundMap f a hL d V W t c k s z
local notation "l" => monicSeedGroundChart f a hL d V W t c k s z
local notation "hu" => monicSeedGround_square f a hL d V W t c k s z
local notation "w" => Over.Hom.left (RelativeCoefficientBaseChange.projection a u w₀)
local notation "T₀" => RelativeCoefficientBaseChange.target a
  (T := finiteKernelModel f hL d V c k)
local notation "j" => fixedBaseJointProjection f a hL d V W t c k l u hu
local notation "r" => fixedBaseJointToGroundOld f a hL d V W t c k l u hu


local instance canonicalGroundTranslationEtale : Etale (W).hom :=
  inferInstanceAs (Etale (pullback.snd V.hom a))
local instance canonicalGroundTranslationAffine : IsAffine (W).left :=
  inferInstanceAs (IsAffine (pullback V.hom a))
local instance canonicalGroundTranslationSurjective :
    Surjective (RelativeCoefficientBaseChange.projection a t (𝟙 V)).left := by
  rw [RelativeCoefficientBaseChange.canonical_projection]
  exact inferInstanceAs (Surjective (𝟙 (W).left))
local instance canonicalGroundSelectedEtale : Etale (v ≫ w₀).left :=
  monicSeedAffineChart_target_etale f hL d V c k s z (w₀).left
    (congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k))
local instance canonicalGroundOldEtale : Etale w :=
  monicSeedGroundOld_etale_arbitrary f a hL d V W t k c s z
attribute [local irreducible] relation fst snd finiteKernelProjection finiteKernelModel
  fixedBaseJointProjection fixedBaseJointTarget fixedBaseJointToOld fixedBaseJointToNew

omit [IsAffine V.left] [Etale s]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- The complete coefficient image equals the entire pulled-back SELECTED old image. -/
theorem monicSeedCanonicalGround_image_eq :
    SchemeEtaleImageQuotient.image w =
      (RelativeCoefficientBaseChange.toOld a
        (T := finiteKernelModel f hL d V c k)).left ⁻¹ᵁ
          SchemeEtaleImageQuotient.image (v ≫ w₀).left :=
  monicSeedGround_image_eq_preimage f a hL d V W t k c s z

/-- Arbitrary ground change preserves the actual selected quotient as a scheme. -/
def monicSeedCanonicalGroundEffectiveIso :
    ((RelativeCoefficientBaseChange.toOld a
      (T := finiteKernelModel f hL d V c k)).left ⁻¹ᵁ
        SchemeEtaleImageQuotient.image (v ≫ w₀).left).toScheme ≅
          (SchemeFppfTargetOpen.locus j).toScheme :=
  (T₀).left.isoOfEq (monicSeedCanonicalGround_image_eq f a hL d V c k s z).symm ≪≫
    monicSeedArbitraryGroundJointEffectiveIso f a hL d V W t c k s z

/-- The full old coefficient map is retained by the canonical effective isomorphism. -/
@[reassoc]
theorem monicSeedCanonicalGroundEffectiveIso_toOld :
    (monicSeedCanonicalGroundEffectiveIso f a hL d V c k s z).hom ≫
      (SchemeFppfTargetOpen.locus j).ι ≫ r = ((RelativeCoefficientBaseChange.toOld a
        (T := finiteKernelModel f hL d V c k)).left ⁻¹ᵁ
          SchemeEtaleImageQuotient.image (v ≫ w₀).left).ι := by
  simp only [monicSeedCanonicalGroundEffectiveIso, Iso.trans_hom, Category.assoc,
    monicSeedArbitraryGroundJointEffectiveIso_toOld, Scheme.isoOfEq_hom_ι]

/-- The entire pulled-back selected quotient is identified over the actual new ground base. -/
def monicSeedCanonicalGroundRelativeIso : Over.mk (((RelativeCoefficientBaseChange.toOld a
        (T := finiteKernelModel f hL d V c k)).left ⁻¹ᵁ
          SchemeEtaleImageQuotient.image (v ≫ w₀).left).ι ≫ (T₀).hom) ≅
    monicSeedArbitraryGroundEffectiveOver f a hL d V W t c k s z :=
  Over.isoMk (monicSeedCanonicalGroundEffectiveIso f a hL d V c k s z) (by
    have hb : r ≫ (T₀).hom = (fixedBaseJointOver f a hL d V W t c k l u hu).hom :=
      (RelativeCoefficientBaseChange.projection a
        (fixedBaseJointRelativeToOld f a hL d V W t c k l u hu)
        (𝟙 (finiteKernelModel f hL d V c k))).w
    change (monicSeedCanonicalGroundEffectiveIso f a hL d V c k s z).hom ≫
      (SchemeFppfTargetOpen.locus j).ι ≫
        (fixedBaseJointOver f a hL d V W t c k l u hu).hom = ((RelativeCoefficientBaseChange.toOld a
        (T := finiteKernelModel f hL d V c k)).left ⁻¹ᵁ
          SchemeEtaleImageQuotient.image (v ≫ w₀).left).ι ≫ (T₀).hom
    rw [← hb]
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ (T₀).hom)
      (monicSeedCanonicalGroundEffectiveIso_toOld f a hL d V c k s z))

omit [Etale V.hom] [IsAffine V.left] [IsAffine A.left] [IsOpenImmersion k.left]
  [Etale s] [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- Every compatible old selected point and new ground point survives canonical base change. -/
theorem monicSeedCanonicalGround_exists_point
    (x : (monicSeedAffineSource f hL d V c k s z).left) (y : Spec (.of R'))
    (hxy : (monicSeedAffineSource f hL d V c k s z).hom x = a y) :
    ∃ b : (monicSeedGroundSource f a hL d V W t c k s z).left,
      (u).left b = (v).left x ∧ (monicSeedGroundSource f a hL d V W t c k s z).hom b = y := by
  obtain ⟨b, hb, hy⟩ := groundBaseSource_exists_point_of_relative_surjective
    f a hL d V W t k₀ x y hxy
  refine ⟨b, ?_, hy⟩
  exact congrArg (v).left hb

end HilbertChart.AffineRestriction
end FLT.Mazur
