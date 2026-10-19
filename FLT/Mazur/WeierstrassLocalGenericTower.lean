/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalKernelTower

/-!
# Retaining the original local cubic and quotient squares through a tower

The canonical comparison between specified local equations retains the full
original curve projection. Both the embedded kernel and every transported
original quotient commute with this comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassLocalGenericTower
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R K L A B : Type} [CommRing R] [CommRing K] [CommRing L]
  [CommRing A] [CommRing B] [Algebra R K] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L] [Algebra A K] [Algebra B L]
  (E : WeierstrassCurve R) (W : WeierstrassCurve A) (V : WeierstrassCurve B)
  (C : VariableChange K) (D : VariableChange L)
  (hC : C • E.map (algebraMap R K) = W.map (algebraMap A K))
  (hD : D • E.map (algebraMap R L) = V.map (algebraMap B L))
local notation "k" => Spec.map (CommRingCat.ofHom (algebraMap K L))
local notation "s" => integralCurveStructure (W.map (algebraMap A K))
local notation "s'" => integralCurveStructure (V.map (algebraMap B L))

/-- The second local cubic retains the composite original coefficient square. -/
theorem outerSquare :
    IsPullback (localGenericProjection E V D hD) (s') (integralCurveStructure E)
      (k ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have he : Spec.map (CommRingCat.ofHom (algebraMap R L)) =
      k ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [IsScalarTower.algebraMap_eq R K L, CommRingCat.ofHom_comp, Spec.map_comp]
  rw [← he]
  exact localGenericProjection_isPullback E V D hD

/-- Compare the actual cubics by their original projections and coefficient structures. -/
def comparison : integralCurve (V.map (algebraMap B L)) ⟶
    integralCurve (W.map (algebraMap A K)) :=
  CartesianSectionCoverTower.comparison
    (localGenericProjection_isPullback E W C hC) (outerSquare E V D hD)

/-- The original curve projection is preserved exactly. -/
@[reassoc] theorem comparison_original :
    comparison E W V C D hC hD ≫ localGenericProjection E W C hC =
      localGenericProjection E V D hD :=
  CartesianSectionCoverTower.comparison_original _ _

/-- The comparison lies over the given extension of generic fields. -/
@[reassoc] theorem comparison_structure : comparison E W V C D hC hD ≫ s = s' ≫ k :=
  CartesianSectionCoverTower.comparison_structure _ _

/-- The actual cubics form the Cartesian coefficient-extension square. -/
theorem comparison_isPullback : IsPullback (comparison E W V C D hC hD) (s') (s) k :=
  CartesianSectionCoverTower.comparison_isPullback _ _

/-- The full original embedded kernel comparison respects its inclusion in the local cubic. -/
@[reassoc] theorem comparison_kernel {H : Scheme} (i : H ⟶ integralCurve E) :
    WeierstrassLocalKernelTower.comparison E W V C D hC hD i ≫
        localGenericKernelInclusion E W C hC i =
      localGenericKernelInclusion E V D hD i ≫ comparison E W V C D hC hD := by
  apply localGenericProjection_hom_ext E W C hC
  · rw [Category.assoc, (localGenericKernel_isPullback E W C hC i).w,
      WeierstrassLocalKernelTower.comparison_original_assoc, Category.assoc,
      comparison_original, (localGenericKernel_isPullback E V D hD i).w]
  · simpa only [Category.assoc, comparison_structure] using
      WeierstrassLocalKernelTower.comparison_structure E W V C D hC hD i

variable (F : WeierstrassCurve R) (U : WeierstrassCurve A) (Z : WeierstrassCurve B)
  (C' : VariableChange K) (D' : VariableChange L)
  (hC' : C' • F.map (algebraMap R K) = U.map (algebraMap A K))
  (hD' : D' • F.map (algebraMap R L) = Z.map (algebraMap B L))
  (f : integralCurve E ⟶ integralCurve F)
  (g : integralCurve (W.map (algebraMap A K)) ⟶ integralCurve (U.map (algebraMap A K)))
  (j : integralCurve (V.map (algebraMap B L)) ⟶ integralCurve (Z.map (algebraMap B L)))
  (hg : g ≫ integralCurveStructure (U.map (algebraMap A K)) =
    integralCurveStructure (W.map (algebraMap A K)))
  (hj : j ≫ integralCurveStructure (Z.map (algebraMap B L)) =
    integralCurveStructure (V.map (algebraMap B L)))
  (hgs : g ≫ localGenericProjection F U C' hC' = localGenericProjection E W C hC ≫ f)
  (hjs : j ≫ localGenericProjection F Z D' hD' = localGenericProjection E V D hD ≫ f)

include hg hj hgs hjs in
/-- The actual original quotient square is preserved on both local coefficient models. -/
theorem comparison_quotient :
    j ≫ comparison F U Z C' D' hC' hD' = comparison E W V C D hC hD ≫ g := by
  apply localGenericProjection_hom_ext F U C' hC'
  · rw [Category.assoc, comparison_original, hjs, Category.assoc, hgs,
      comparison_original_assoc]
  · rw [Category.assoc, comparison_structure, ← Category.assoc, hj,
      Category.assoc, hg, comparison_structure]

end FLT.Mazur.WeierstrassLocalGenericTower
