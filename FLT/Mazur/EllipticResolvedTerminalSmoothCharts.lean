/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedTerminalCharts

/-!
# Terminal arithmetic charts in the actual resolved smooth locus

Both odd punctures and the even middle torus lift to the original smooth open.
Their inclusion and arithmetic point formulas recover the original unrestricted smooth point.
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
  (r : (ResidueField A)ˣ) (hk0 : 0 < depth / 2)
local notation "F" => ResidueField A
local notation "p" => resolvedSplitStructure A D

/-- The entire terminal positive torus lies in the original smooth locus. -/
theorem resolvedTerminalPositiveChart_mem_smooth (hp : 2 * (depth / 2) < depth)
    (z : Spec (.of F[T;T⁻¹])) : resolvedTerminalPositiveChart A D r hk0 hp z ∈ (p).smoothLocus := by
  apply (PolygonAtlas.mem_smooth_iff (resolvedTerminalPositiveChart A D r hk0 hp) p z).mpr
  have hs : Smooth (resolvedTerminalPositiveChart A D r hk0 hp ≫ p) := by
    rw [resolvedTerminalPositiveChart_structure]
    infer_instance
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- The terminal positive torus as an actual resolved smooth chart. -/
def resolvedTerminalPositiveSmoothChart (hp : 2 * (depth / 2) < depth) :
    Spec (.of F[T;T⁻¹]) ⟶ (p).smoothLocus.toScheme :=
  IsOpenImmersion.lift (p).smoothLocus.ι (resolvedTerminalPositiveChart A D r hk0 hp) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact resolvedTerminalPositiveChart_mem_smooth A D r hk0 hp z)

instance resolvedTerminalPositiveSmoothChart_isOpenImmersion (hp : 2 * (depth / 2) < depth) :
    IsOpenImmersion (resolvedTerminalPositiveSmoothChart A D r hk0 hp) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- The positive smooth chart retains its original final-model inclusion. -/
@[reassoc] theorem resolvedTerminalPositiveSmoothChart_inclusion (hp : 2 * (depth / 2) < depth) :
    resolvedTerminalPositiveSmoothChart A D r hk0 hp ≫ (p).smoothLocus.ι =
      resolvedTerminalPositiveChart A D r hk0 hp := IsOpenImmersion.lift_fac _ _ _

/-- The entire terminal negative torus lies in the original smooth locus. -/
theorem resolvedTerminalNegativeChart_mem_smooth (hp : 2 * (depth / 2) < depth)
    (z : Spec (.of F[T;T⁻¹])) : resolvedTerminalNegativeChart A D r hk0 hp z ∈ (p).smoothLocus := by
  apply (PolygonAtlas.mem_smooth_iff (resolvedTerminalNegativeChart A D r hk0 hp) p z).mpr
  have hs : Smooth (resolvedTerminalNegativeChart A D r hk0 hp ≫ p) := by
    rw [resolvedTerminalNegativeChart_structure]
    infer_instance
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- The terminal negative torus as an actual resolved smooth chart. -/
def resolvedTerminalNegativeSmoothChart (hp : 2 * (depth / 2) < depth) :
    Spec (.of F[T;T⁻¹]) ⟶ (p).smoothLocus.toScheme :=
  IsOpenImmersion.lift (p).smoothLocus.ι (resolvedTerminalNegativeChart A D r hk0 hp) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact resolvedTerminalNegativeChart_mem_smooth A D r hk0 hp z)

instance resolvedTerminalNegativeSmoothChart_isOpenImmersion (hp : 2 * (depth / 2) < depth) :
    IsOpenImmersion (resolvedTerminalNegativeSmoothChart A D r hk0 hp) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- The negative smooth chart retains its original final-model inclusion. -/
@[reassoc] theorem resolvedTerminalNegativeSmoothChart_inclusion (hp : 2 * (depth / 2) < depth) :
    resolvedTerminalNegativeSmoothChart A D r hk0 hp ≫ (p).smoothLocus.ι =
      resolvedTerminalNegativeChart A D r hk0 hp := IsOpenImmersion.lift_fac _ _ _

/-- The entire terminal middle torus lies in the original smooth locus. -/
theorem resolvedTerminalMiddleChart_mem_smooth (hm : 2 * (depth / 2) = depth)
    (z : Spec (.of F[T;T⁻¹])) : resolvedTerminalMiddleChart A D r hk0 hm z ∈ (p).smoothLocus := by
  apply (PolygonAtlas.mem_smooth_iff (resolvedTerminalMiddleChart A D r hk0 hm) p z).mpr
  have hs : Smooth (resolvedTerminalMiddleChart A D r hk0 hm ≫ p) := by
    rw [resolvedTerminalMiddleChart_structure]
    infer_instance
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- The terminal middle torus as an actual resolved smooth chart. -/
def resolvedTerminalMiddleSmoothChart (hm : 2 * (depth / 2) = depth) :
    Spec (.of F[T;T⁻¹]) ⟶ (p).smoothLocus.toScheme :=
  IsOpenImmersion.lift (p).smoothLocus.ι (resolvedTerminalMiddleChart A D r hk0 hm) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact resolvedTerminalMiddleChart_mem_smooth A D r hk0 hm z)

instance resolvedTerminalMiddleSmoothChart_isOpenImmersion (hm : 2 * (depth / 2) = depth) :
    IsOpenImmersion (resolvedTerminalMiddleSmoothChart A D r hk0 hm) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- The middle smooth chart retains its original final-model inclusion. -/
@[reassoc] theorem resolvedTerminalMiddleSmoothChart_inclusion (hm : 2 * (depth / 2) = depth) :
    resolvedTerminalMiddleSmoothChart A D r hk0 hm ≫ (p).smoothLocus.ι =
      resolvedTerminalMiddleChart A D r hk0 hm := IsOpenImmersion.lift_fac _ _ _

variable (c₆ : A) (h6 : W.a₆ = π ^ depth * c₆)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = depth / 2)
local notation "pt" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (LaurentUnitPoints.evalUnit (R := F) (nodeTrivializedParameter D c₆ h6 r P))))

include hv in
/-- The terminal positive parameter recovers the actual unrestricted smooth point. -/
theorem resolvedTerminalPositiveSmoothChart_point (hp : 2 * (depth / 2) < depth)
    (hb : v.b ∈ maximalIdeal A) :
    pt ≫ resolvedTerminalPositiveSmoothChart A D r hk0 hp = resolvedSplitSmoothPoint A D P := by
  apply (cancel_mono (p).smoothLocus.ι).mp
  rw [Category.assoc, resolvedTerminalPositiveSmoothChart_inclusion,
    resolvedSplitSmoothPoint_inclusion]
  exact resolvedTerminalPositiveChart_specialization A D r hk0 c₆ h6 P v hv hp hb

include hv in
/-- The terminal negative parameter recovers the actual unrestricted smooth point. -/
theorem resolvedTerminalNegativeSmoothChart_point (hp : 2 * (depth / 2) < depth)
    (hr : r ^ depth = nodeWrapParameterUnit D c₆ h6) (hb : IsUnit v.b) :
    pt ≫ resolvedTerminalNegativeSmoothChart A D r hk0 hp = resolvedSplitSmoothPoint A D P := by
  apply (cancel_mono (p).smoothLocus.ι).mp
  rw [Category.assoc, resolvedTerminalNegativeSmoothChart_inclusion,
    resolvedSplitSmoothPoint_inclusion]
  exact resolvedTerminalNegativeChart_specialization A D r hk0 c₆ h6 P v hv hp hr hb

include hv in
/-- The terminal middle parameter recovers the actual unrestricted smooth point. -/
theorem resolvedTerminalMiddleSmoothChart_point (hm : 2 * (depth / 2) = depth)
    (hr : r ^ depth = nodeWrapParameterUnit D c₆ h6) :
    pt ≫ resolvedTerminalMiddleSmoothChart A D r hk0 hm = resolvedSplitSmoothPoint A D P := by
  apply (cancel_mono (p).smoothLocus.ι).mp
  rw [Category.assoc, resolvedTerminalMiddleSmoothChart_inclusion,
    resolvedSplitSmoothPoint_inclusion]
  exact resolvedTerminalMiddleChart_specialization A D r hk0 c₆ h6 P v hv hm hr

end FLT.Mazur.WeierstrassDividedDepth
