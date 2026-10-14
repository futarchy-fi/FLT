/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGroundRelativeEtale
public import FLT.Mazur.AffineHilbertFixedBaseJointGroundEtale

/-!
# Effective seed models after arbitrary ground changes

The source, its etale old coefficient map, and its FULL original kernel are
constructed from the seed. The resulting joint effective scheme retains both
coefficient systems under arbitrary ground changes and etale translations
over their own ground bases. No absolute etaleness assumption is imposed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => Limits.pullback.snd f a
local instance monicSeedArbitraryGroundSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  [Etale V.hom] [Etale W.hom]
  {Z : Scheme} (s : Z ⟶ A.left) [Etale s]
  [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)]
  [Mono (s ≫ (finiteKernelProjection f hL d V c k).left)]
  (z : (pullback (snd f hL d V c k).left s : Scheme))
variable [IsAffine V.left] [IsAffine W.left]
local notation "l" => monicSeedGroundChart f a hL d V W t c k s z
local notation "u" => monicSeedGroundMap f a hL d V W t c k s z
local notation "hu" => monicSeedGround_square f a hL d V W t c k s z
local notation "w" => Over.Hom.left (RelativeCoefficientBaseChange.projection a u
  (finiteKernelProjection f hL d V c k))
local instance seedArbitraryGroundOldEtale : Etale w :=
  monicSeedGroundOld_etale_arbitrary f a hL d V W t k c s z
local notation "H" => monicSeedGroundOld_isPullback f a hL d V W t c k s z
local notation "j" => fixedBaseJointProjection f a hL d V W t c k l u hu
local notation "hj" => fixedBaseJointProjection_condition f a hL d V W t c k l u hu
local notation "r" => fixedBaseJointToGroundOld f a hL d V W t c k l u hu
local notation "hr" => fixedBaseJointProjection_toGroundOld f a hL d V W t c k l u hu
attribute [local irreducible] relation fst snd finiteKernelProjection finiteKernelModel
  fixedBaseJointProjection fixedBaseJointTarget fixedBaseJointToOld fixedBaseJointToNew

/-- The whole constructed changed-source joint projection is etale. -/
theorem monicSeedArbitraryGroundJoint_etale : Etale j :=
  fixedBaseJointProjection_etale_of_groundOld f a hL d V W t c k l u hu H

/-- The effective open is an actual scheme quotient with all certificates constructed. -/
def monicSeedArbitraryGroundJointEffectiveIso : (SchemeEtaleImageQuotient.image w).toScheme ≅
    (SchemeFppfTargetOpen.locus j).toScheme :=
  fixedBaseJointGroundEffectiveIso f a hL d V W t c k l u hu H

/-- The quotient comparison retains the entire ground-aware old coefficient scheme map. -/
@[reassoc]
theorem monicSeedArbitraryGroundJointEffectiveIso_toOld :
    (monicSeedArbitraryGroundJointEffectiveIso f a hL d V W t c k s z).hom ≫
      (SchemeFppfTargetOpen.locus j).ι ≫ r = (SchemeEtaleImageQuotient.image w).ι :=
  SchemeEtaleImageDenseModel.effectiveIso_toOld w H j hj r hr

/-- Every test is covered by the COMPLETE changed source, with both endpoints retained. -/
theorem monicSeedArbitraryGroundJoint_complete_cover {Y : Scheme}
    (b : Y ⟶ (SchemeEtaleImageQuotient.image w).toScheme) :
    Etale (SchemeEtaleImageDenseModel.completeProjection w H j hj b) ∧
    Surjective (SchemeEtaleImageDenseModel.completeProjection w H j hj b) :=
  fixedBaseJointGround_complete_cover f a hL d V W t c k l u hu H b

/-- Both old and freshly recomputed coefficients survive on arbitrary complete source tests. -/
theorem monicSeedArbitraryGroundJoint_complete_coefficients {Y : Scheme}
    (b : Y ⟶ (SchemeEtaleImageQuotient.image w).toScheme) :
    SchemeEtaleImageDenseModel.completeToSource w H j hj b ≫ w =
      SchemeEtaleImageDenseModel.completeProjection w H j hj b ≫ b ≫
        (SchemeEtaleImageQuotient.image w).ι ∧
    SchemeEtaleImageDenseModel.completeToSource w H j hj b ≫
      (finiteKernelProjection q h d W c' l).left =
        SchemeEtaleImageDenseModel.completeProjection w H j hj b ≫ b ≫
          SchemeEtaleImageDenseModel.comparison w H j hj ≫
            fixedBaseJointToNew f a hL d V W t c k l u hu :=
  fixedBaseJointGround_complete_coefficients f a hL d V W t c k l u hu H b

local notation "T₀" => RelativeCoefficientBaseChange.target a
  (T := finiteKernelModel f hL d V c k)
local notation "J" => fixedBaseJointOver f a hL d V W t c k l u hu

/-- The actual old image with its new ground structure, for arbitrary ground change. -/
def monicSeedArbitraryGroundImageOver : Over (Spec (.of R')) :=
  Over.mk ((SchemeEtaleImageQuotient.image w).ι ≫ (T₀).hom)

/-- The effective joint open with its new ground structure. -/
def monicSeedArbitraryGroundEffectiveOver : Over (Spec (.of R')) :=
  Over.mk ((SchemeFppfTargetOpen.locus j).ι ≫ (J).hom)

/-- The constructed quotient isomorphism is over the new ground base, without reducing it. -/
def monicSeedArbitraryGroundRelativeIso :
    monicSeedArbitraryGroundImageOver f a hL d V W t c k s z ≅
      monicSeedArbitraryGroundEffectiveOver f a hL d V W t c k s z :=
  Over.isoMk (monicSeedArbitraryGroundJointEffectiveIso f a hL d V W t c k s z) (by
    have hb : r ≫ (T₀).hom = (J).hom :=
      (RelativeCoefficientBaseChange.projection a
        (fixedBaseJointRelativeToOld f a hL d V W t c k l u hu)
        (𝟙 (finiteKernelModel f hL d V c k))).w
    change (monicSeedArbitraryGroundJointEffectiveIso f a hL d V W t c k s z).hom ≫
      (SchemeFppfTargetOpen.locus j).ι ≫ (J).hom =
        (SchemeEtaleImageQuotient.image w).ι ≫ (T₀).hom
    rw [← hb]
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ (T₀).hom)
      (monicSeedArbitraryGroundJointEffectiveIso_toOld f a hL d V W t c k s z))

/-- The relative isomorphism retains the full joint coefficient morphism. -/
@[reassoc]
theorem monicSeedArbitraryGroundRelativeIso_ι :
    (monicSeedArbitraryGroundRelativeIso f a hL d V W t c k s z).hom.left ≫
      (SchemeFppfTargetOpen.locus j).ι = SchemeEtaleImageDenseModel.comparison w H j hj :=
  SchemeEtaleImageDenseModel.effectiveIso_ι w H j hj r hr

end FLT.Mazur.HilbertChart.AffineRestriction
