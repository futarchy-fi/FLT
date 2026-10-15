/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedIdentityCharacter
public import FLT.Mazur.PolygonSplitIdentityGroup

/-!
# Reciprocal orientation of the actual resolved identity torus

The original torus is reparametrized by the existing reciprocal group
isomorphism. Its full image and coefficient map are unchanged, and the
arithmetic smooth character itself now reconstructs proper specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "F" => ResidueField A
local notation "p" => resolvedSplitStructure A D
local notation "torus" => Spec (CommRingCat.of (LaurentPolynomial F))

/-- The complete original identity torus with reciprocal cyclic orientation. -/
def resolvedReciprocalIdentitySmoothChart : torus ⟶ (p).smoothLocus.toScheme :=
  (ProjectiveLine.inversion F).hom ≫ resolvedIdentitySmoothChart A D

instance resolvedReciprocalIdentitySmoothChart_isOpenImmersion :
    IsOpenImmersion (resolvedReciprocalIdentitySmoothChart A D) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Reciprocal orientation preserves the complete original identity component image. -/
theorem resolvedReciprocalIdentitySmoothChart_range :
    Set.range (resolvedReciprocalIdentitySmoothChart A D) =
      Set.range (resolvedIdentitySmoothChart A D) :=
  SchemeOpenChartRange.range_iso_comp (ProjectiveLine.inversion F) _

/-- The reciprocal identity chart keeps the original full resolved-fiber inclusion. -/
@[reassoc] theorem resolvedReciprocalIdentitySmoothChart_inclusion :
    resolvedReciprocalIdentitySmoothChart A D ≫ (p).smoothLocus.ι =
      (ProjectiveLine.inversion F).hom ≫ resolvedIdentityChart A D := by
  rw [resolvedReciprocalIdentitySmoothChart, Category.assoc,
    resolvedIdentitySmoothChart_inclusion]

/-- The reciprocal chart is over the unchanged original residue spectrum. -/
@[reassoc] theorem resolvedReciprocalIdentitySmoothChart_structure :
    resolvedReciprocalIdentitySmoothChart A D ≫ (p).smoothLocus.ι ≫ p =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [resolvedReciprocalIdentitySmoothChart_inclusion_assoc,
    resolvedIdentityChart_structure, ← PolygonSplitGroup.reciprocalGroupIso_left]
  exact (PolygonSplitGroup.reciprocalGroupIso F).hom.hom.hom.hom.w

variable [DecidableEq (ResidueField A)]

/-- The original arithmetic smooth character itself gives the reciprocal chart coordinate. -/
@[reassoc] theorem resolvedReciprocalIdentitySmoothChart_point (P : ellipticE0 A W) :
    ProjectiveLineActionSpecialization.unitPoint F
        (Additive.toMul (splitDepthSmoothCharacter D P)) ≫
      resolvedReciprocalIdentitySmoothChart A D = resolvedSplitSmoothPoint A D P.val := by
  rw [resolvedReciprocalIdentitySmoothChart, ← Category.assoc,
    ProjectiveLineMarkedCharts.unitPoint_inversion]
  change resolvedIdentityCharacterPoint A D P ≫ resolvedIdentitySmoothChart A D = _
  rw [← resolvedIdentityPointCoordinate_character, resolvedIdentityPointCoordinate_smoothChart]

end FLT.Mazur.WeierstrassDividedDepth
