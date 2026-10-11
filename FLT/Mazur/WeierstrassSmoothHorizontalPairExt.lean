/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalPairDensity
public import FLT.Mazur.ProjectiveLineProductChartTorusExt
public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# The original horizontal pair detects the whole group-times-component morphism

Density of the actual independent pair fills in the omitted smooth parameters.
Density of the chosen projective chart puncture then fills in both endpoints.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "q" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (ProjectiveLineUniversalAction.laurentPairEvaluation τ⁻¹ z)))

/-- Equality on either original horizontal pair determines the full relative product map. -/
theorem smoothHorizontalPair_hom_ext {Y : Over (Spec (.of K))} [IsSeparated Y.hom]
    (f g : MultiplicativeGroupScheme.gm K ⊗ PolygonPinching.component K ⟶ Y)
    (b : Bool)
    (h : q ≫ ProjectiveLineProductOverlap.left L ≫
        ProjectiveLineProductCharts.productChartMap K L b ≫ f.left =
      q ≫ ProjectiveLineProductOverlap.left L ≫
        ProjectiveLineProductCharts.productChartMap K L b ≫ g.left) : f = g := by
  apply Over.OverMorphism.ext
  apply ProjectiveLineProductCharts.product_hom_ext_chart_overlap K L Y.hom
    f.left g.left (f.w.trans g.w.symm) b
  apply ext_of_isDominant_of_isSeparated Y.hom _ q h
  simpa only [Category.assoc] using congrArg
    ((ProjectiveLineProductOverlap.left L ≫
      ProjectiveLineProductCharts.productChartMap K L b) ≫ ·) (f.w.trans g.w.symm)

end FLT.Mazur.WeierstrassIntegralChart
