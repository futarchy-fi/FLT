/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertMonicSeedGroundEtale

/-!
# Relative effective seed quotients over the new ground base

The effective comparison is an isomorphism over the NEW ground base, with
the full old coefficient and freshly recomputed coefficient maps retained.
All kernel and etaleness certificates come from the constructed seed chart.
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
local instance monicSeedGroundRelativeSmooth : SmoothOfRelativeDimension 1 q :=
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
variable [Etale a] [Etale t.left] [IsAffine V.left] [IsAffine W.left]
local notation "l" => monicSeedGroundChart f a hL d V W t c k s z
local notation "u" => monicSeedGroundMap f a hL d V W t c k s z
local notation "hu" => monicSeedGround_square f a hL d V W t c k s z
local notation "w" => Over.Hom.left (RelativeCoefficientBaseChange.projection a u
  (finiteKernelProjection f hL d V c k))
local instance seedGroundRelativeOldEtale : Etale w :=
  monicSeedGroundOld_etale f a hL d V W t c k s z
local notation "H" => monicSeedGroundOld_isPullback f a hL d V W t c k s z
local notation "j" => fixedBaseJointProjection f a hL d V W t c k l u hu
local notation "hj" => fixedBaseJointProjection_condition f a hL d V W t c k l u hu
local notation "r" => fixedBaseJointToGroundOld f a hL d V W t c k l u hu
local notation "hr" => fixedBaseJointProjection_toGroundOld f a hL d V W t c k l u hu
attribute [local irreducible] relation fst snd finiteKernelProjection finiteKernelModel
  fixedBaseJointProjection fixedBaseJointTarget fixedBaseJointToOld fixedBaseJointToNew

local notation "T₀" => RelativeCoefficientBaseChange.target a
  (T := finiteKernelModel f hL d V c k)
local notation "J" => fixedBaseJointOver f a hL d V W t c k l u hu

omit [Etale a] [Etale t.left]
  [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- The full original changed Picard relation is the COMPLETE joint coefficient kernel. -/
theorem monicSeedGroundJoint_isPullback :
    IsPullback (fst q h d W c' l).left (snd q h d W c' l).left j j := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hj
    (fun c ↦ (H).lift c.fst c.snd (by
      rw [← hr, ← Category.assoc, ← Category.assoc, c.condition]))
    (fun _ ↦ (H).lift_fst _ _ _) (fun _ ↦ (H).lift_snd _ _ _) ?_)
  intro c b hb₁ hb₂
  apply (H).hom_ext
  · exact hb₁.trans ((H).lift_fst _ _ _).symm
  · exact hb₂.trans ((H).lift_snd _ _ _).symm

/-- The old actual coefficient image over the new original ground base. -/
def monicSeedGroundImageOver : Over (Spec (.of R')) :=
  Over.mk ((SchemeEtaleImageQuotient.image w).ι ≫ (T₀).hom)

/-- The effective joint open with its actual new ground structure. -/
def monicSeedGroundEffectiveOver : Over (Spec (.of R')) :=
  Over.mk ((SchemeFppfTargetOpen.locus j).ι ≫ (J).hom)

omit [Etale a] [Etale t.left]
  [Etale (s ≫ (finiteKernelProjection f hL d V c k).left)] in
/-- Both new ground structure maps are retained by the actual joint comparison. -/
theorem monicSeedGroundJointToOld_over : r ≫ (T₀).hom = (J).hom :=
  (RelativeCoefficientBaseChange.projection a
    (fixedBaseJointRelativeToOld f a hL d V W t c k l u hu)
    (𝟙 (finiteKernelModel f hL d V c k))).w

/-- The constructed effective comparison is an isomorphism over the new coefficient base. -/
def monicSeedGroundRelativeEffectiveIso : monicSeedGroundImageOver f a hL d V W t c k s z ≅
    monicSeedGroundEffectiveOver f a hL d V W t c k s z :=
  Over.isoMk (monicSeedGroundJointEffectiveIso f a hL d V W t c k s z) (by
    change (monicSeedGroundJointEffectiveIso f a hL d V W t c k s z).hom ≫
      (SchemeFppfTargetOpen.locus j).ι ≫ (J).hom =
        (SchemeEtaleImageQuotient.image w).ι ≫ (T₀).hom
    rw [← monicSeedGroundJointToOld_over f a hL d V W t c k s z]
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ (T₀).hom)
      (monicSeedGroundJointEffectiveIso_toOld f a hL d V W t c k s z))

/-- The relative isomorphism retains the entire joint scheme map, including nilpotents. -/
@[reassoc]
theorem monicSeedGroundRelativeEffectiveIso_ι :
    (monicSeedGroundRelativeEffectiveIso f a hL d V W t c k s z).hom.left ≫
      (SchemeFppfTargetOpen.locus j).ι = SchemeEtaleImageDenseModel.comparison w H j hj :=
  SchemeEtaleImageDenseModel.effectiveIso_ι w H j hj r hr

/-- Fresh finite coefficients remain the actual scheme map under the relative isomorphism. -/
@[reassoc]
theorem monicSeedGroundRelativeEffectiveIso_toNew :
    (monicSeedGroundRelativeEffectiveIso f a hL d V W t c k s z).hom.left ≫
      (SchemeFppfTargetOpen.locus j).ι ≫
        fixedBaseJointToNew f a hL d V W t c k l u hu =
    SchemeEtaleImageDenseModel.comparison w H j hj ≫
      fixedBaseJointToNew f a hL d V W t c k l u hu := by
  rw [monicSeedGroundRelativeEffectiveIso_ι_assoc]

end FLT.Mazur.HilbertChart.AffineRestriction
