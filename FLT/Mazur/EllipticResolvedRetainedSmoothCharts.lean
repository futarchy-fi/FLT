/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedRetainedCharts

/-!
# Retained arithmetic charts in the actual resolved smooth locus

Both punctures lift to the original smooth open. Their inclusion and arithmetic
point formulas agree with the previously constructed unrestricted smooth point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (j : ℕ) (hj0 : 0 < j) (hj : j < depth / 2)
local notation "F" => ResidueField A
local notation "p" => resolvedSplitStructure A D
local notation "pos" => resolvedRetainedPositiveChart A D r j hj0 hj
local notation "neg" => resolvedRetainedNegativeChart A D r j hj0 hj

/-- Every point of the retained positive torus lies in the original smooth locus. -/
theorem resolvedRetainedPositiveChart_mem_smooth (z : Spec (.of F[T;T⁻¹])) :
    pos z ∈ (p).smoothLocus := by
  apply (PolygonAtlas.mem_smooth_iff pos p z).mpr
  have hs : Smooth (pos ≫ p) := by
    rw [resolvedRetainedPositiveChart_structure]
    infer_instance
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- Every point of the retained negative torus lies in the original smooth locus. -/
theorem resolvedRetainedNegativeChart_mem_smooth (z : Spec (.of F[T;T⁻¹])) :
    neg z ∈ (p).smoothLocus := by
  apply (PolygonAtlas.mem_smooth_iff neg p z).mpr
  have hs : Smooth (neg ≫ p) := by
    rw [resolvedRetainedNegativeChart_structure]
    infer_instance
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- The positive arithmetic torus as an actual chart in the original resolved smooth open. -/
def resolvedRetainedPositiveSmoothChart :
    Spec (.of F[T;T⁻¹]) ⟶ (p).smoothLocus.toScheme :=
  IsOpenImmersion.lift (p).smoothLocus.ι pos (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact resolvedRetainedPositiveChart_mem_smooth A D r j hj0 hj z)

/-- The negative arithmetic torus as an actual chart in the original resolved smooth open. -/
def resolvedRetainedNegativeSmoothChart :
    Spec (.of F[T;T⁻¹]) ⟶ (p).smoothLocus.toScheme :=
  IsOpenImmersion.lift (p).smoothLocus.ι neg (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact resolvedRetainedNegativeChart_mem_smooth A D r j hj0 hj z)

instance resolvedRetainedPositiveSmoothChart_isOpenImmersion :
    IsOpenImmersion (resolvedRetainedPositiveSmoothChart A D r j hj0 hj) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

instance resolvedRetainedNegativeSmoothChart_isOpenImmersion :
    IsOpenImmersion (resolvedRetainedNegativeSmoothChart A D r j hj0 hj) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- The positive smooth chart includes as its original final-model chart. -/
@[reassoc] theorem resolvedRetainedPositiveSmoothChart_inclusion :
    resolvedRetainedPositiveSmoothChart A D r j hj0 hj ≫ (p).smoothLocus.ι = pos :=
  IsOpenImmersion.lift_fac _ _ _

/-- The negative smooth chart includes as its original final-model chart. -/
@[reassoc] theorem resolvedRetainedNegativeSmoothChart_inclusion :
    resolvedRetainedNegativeSmoothChart A D r j hj0 hj ≫ (p).smoothLocus.ι = neg :=
  IsOpenImmersion.lift_fac _ _ _

variable (c₆ : A) (h6 : W.a₆ = π ^ depth * c₆)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = j)
local notation "pt" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (LaurentUnitPoints.evalUnit (R := F) (nodeTrivializedParameter D c₆ h6 r P))))

include hv in
/-- The positive arithmetic parameter recovers the original unrestricted smooth point. -/
theorem resolvedRetainedPositiveSmoothChart_point (hb : v.b ∈ maximalIdeal A) :
    pt ≫ resolvedRetainedPositiveSmoothChart A D r j hj0 hj = resolvedSplitSmoothPoint A D P := by
  apply (cancel_mono (p).smoothLocus.ι).mp
  rw [Category.assoc, resolvedRetainedPositiveSmoothChart_inclusion,
    resolvedSplitSmoothPoint_inclusion]
  exact resolvedRetainedPositiveChart_specialization A D r j hj0 hj c₆ h6 P v hv hb

include hv in
/-- The negative arithmetic parameter recovers the original unrestricted smooth point. -/
theorem resolvedRetainedNegativeSmoothChart_point
    (hr : r ^ depth = nodeWrapParameterUnit D c₆ h6) (hb : IsUnit v.b) :
    pt ≫ resolvedRetainedNegativeSmoothChart A D r j hj0 hj = resolvedSplitSmoothPoint A D P := by
  apply (cancel_mono (p).smoothLocus.ι).mp
  rw [Category.assoc, resolvedRetainedNegativeSmoothChart_inclusion,
    resolvedSplitSmoothPoint_inclusion]
  exact resolvedRetainedNegativeChart_specialization A D r j hj0 hj c₆ h6 P v hv hr hb

end FLT.Mazur.WeierstrassDividedDepth
