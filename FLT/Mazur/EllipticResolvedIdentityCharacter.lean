/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitDepthLaurentContraction
public import FLT.Mazur.EllipticResolvedIdentityPoints
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothActionUnique

/-!
# The actual resolved identity coordinate is the inverse smooth character

Both the original contraction and residue-field structure are retained.
Uniqueness over the unchanged original smooth open identifies the actual
coordinate morphism, rather than only its equality relation on points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  [DecidableEq (ResidueField A)]
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "q" => Spec.map (CommRingCat.ofHom (residue A))
local notation "f" => finiteGlobalStructure hπ data (depth / 2) (le_refl _)
local notation "c" => finiteGlobalContraction hπ data (depth / 2) (le_refl _)
local notation "sp" => finitePointSpecialization A hπ data (depth / 2) (le_refl _)

/-- The inverse smooth character, as an actual residue-field point of the original torus. -/
def resolvedIdentityCharacterPoint (P : ellipticE0 A W) :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := F)
    (Additive.toMul (splitDepthSmoothCharacter D P))⁻¹).toRingHom)

/-- The inverse-character Laurent point retains the original residue-field structure. -/
@[reassoc] theorem resolvedIdentityCharacterPoint_structure (P : ellipticE0 A W) :
    resolvedIdentityCharacterPoint A D P ≫ (MultiplicativeGroupScheme.gm F).hom = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have he : (LaurentUnitPoints.evalUnit (R := F)
      (Additive.toMul (splitDepthSmoothCharacter D P))⁻¹).toRingHom.comp
        (algebraMap F (LaurentPolynomial F)) = RingHom.id F := by
    ext x
    exact (LaurentUnitPoints.evalUnit (R := F)
      (Additive.toMul (splitDepthSmoothCharacter D P))⁻¹).commutes x
  change Spec.map (CommRingCat.ofHom
    ((LaurentUnitPoints.evalUnit (R := F)
      (Additive.toMul (splitDepthSmoothCharacter D P))⁻¹).toRingHom.comp
        (algebraMap F (LaurentPolynomial F)))) = _
  rw [he]
  exact Spec.map_id _

/-- The inverse-character Laurent point contracts to the actual original smooth reduction. -/
@[reassoc] theorem resolvedIdentityCharacterPoint_contraction (P : ellipticE0 A W) :
    resolvedIdentityCharacterPoint A D P ≫ infinityResidueContraction D D.depth_pos =
      (projectiveToIntegral W (smoothReductionHom A W P)).left :=
  splitDepthLaurent_inverse_character_contraction D (smoothReductionHom A W P)

/-- The inverse-character point recovers the original unrestricted proper specialization. -/
@[reassoc] theorem resolvedIdentityCharacterPoint_chart (P : ellipticE0 A W) :
    resolvedIdentityCharacterPoint A D P ≫ resolvedIdentityChart A D = sp P.val := by
  apply pullback.hom_ext
  · change _ ≫ resolvedSplitStructure A D = _
    rw [Category.assoc, resolvedIdentityChart_structure,
      resolvedIdentityCharacterPoint_structure]
    exact (finitePointSpecialization_structure A hπ data (depth / 2) (le_refl _) P.val).symm
  · apply finiteGlobal_smooth_output_hom_ext hπ data (depth / 2) (le_refl _)
      (projectiveToSmooth W (smoothReductionHom A W P))
    · rw [Category.assoc, Category.assoc, resolvedIdentityChart_contraction,
        resolvedIdentityCharacterPoint_contraction, projectiveToSmooth_inclusion]
    · change sp P.val ≫ pullback.snd q f ≫ c = _
      rw [finitePointSpecialization_contraction,
        integralPointSpecialization_eq_projective A W P.val P.property,
        projectiveToSmooth_inclusion]
      rfl

/-- The actual identity coordinate is evaluation at the inverse arithmetic smooth character. -/
theorem resolvedIdentityPointCoordinate_character (P : ellipticE0 A W) :
    resolvedIdentityPointCoordinate A D P = resolvedIdentityCharacterPoint A D P := by
  apply (cancel_mono (resolvedIdentityChart A D)).mp
  rw [resolvedIdentityPointCoordinate_chart, resolvedIdentityCharacterPoint_chart]

end FLT.Mazur.WeierstrassDividedDepth
