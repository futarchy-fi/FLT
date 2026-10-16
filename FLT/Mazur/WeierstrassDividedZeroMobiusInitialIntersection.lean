/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroMobiusInitialOverlap
public import FLT.Mazur.WeierstrassModificationXZeroMobiusPuncturePreimage

/-!
# No extra intersections between the two original fractional initial charts

Equality in the complete polygon forces a point of the first initial chart
into the original D(q) overlap. The original overlap equality and the second
chart's open immersion then recover equality in the original affine scheme.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (k : ℕ)
local instance zeroMobiusIntersection_nilpotent : Fact (IsNilpotent (0 : R)) := ⟨1, by simp⟩
local notation "L" => PolynomialNodeOpen W 0

/-- The two initial labels have just their intended edge, since the polygon has at least 3 nodes. -/
theorem initialPolygonIndex_not_reverse_preceding :
    (finRotate (2 * k + 3)).symm (initialPolygonIndex k false) ≠ initialPolygonIndex k true := by
  let _ : NeZero (2 * k + 3) := ⟨by omega⟩
  intro h
  have ht := (finRotate_symm_lt_iff_ne_zero (i := initialPolygonIndex k false)).mpr
    (initialPolygonIndex_ne_terminal k false)
  rw [h] at ht
  change k + 2 < k + 1 at ht
  omega

/-- Any cross-label equality in the polygon comes from the entire original node overlap. -/
theorem zeroInitialMobiusPolygonMap_cross_preimage (x y : Spec (.of L))
    (h : zeroInitialMobiusPolygonMap W ha k false x =
      zeroInitialMobiusPolygonMap W ha k true y) :
    x ∈ Set.range (polynomialNodeOverlapInclusion W 0) := by
  have hn : initialPolygonIndex k false ≠ initialPolygonIndex k true := by
    intro he
    have := initialPolygonIndex_injective k he
    contradiction
  have he : PolygonInfinitesimal.chart R 0 (2 * k + 3) (by omega)
      (initialPolygonIndex k false) (zeroInitialMobiusChart W ha x) =
    PolygonInfinitesimal.chart R 0 (2 * k + 3) (by omega)
      (initialPolygonIndex k true) ((branchSwapIso R 0).hom (zeroInitialMobiusChart W ha y)) := h
  rcases (PolygonInfinitesimal.charts_eq_iff R 0 (2 * k + 3) (by omega) hn _ _).mp he with
    ⟨z, hz, _, _⟩ | ⟨z, _, hx, _⟩
  · exact (initialPolygonIndex_not_reverse_preceding k hz).elim
  · rw [← zeroInitialMobiusChart_right_preimage W ha]
    exact ⟨(edgeInversion R).hom z, hx⟩

variable (b3 b4 b6 : R) (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I) (hbot : I = ⊥)

include hbot in
/-- Cross-label equality introduces no identifications beyond the original initial affine scheme. -/
theorem zeroInitialMobiusPolygonMap_cross_eq (x y : Spec (.of L))
    (h : zeroInitialMobiusPolygonMap W ha k false x =
      zeroInitialMobiusPolygonMap W ha k true y) :
    polynomialNodeChart W 0 b3 b4 b6 r hr I hI hrI h3 x =
      polynomialOppositeNodeChart W 0 b3 b4 b6 r hr I hI hrI h3 y := by
  obtain ⟨z, rfl⟩ := zeroInitialMobiusPolygonMap_cross_preimage W ha k x y h
  have he := congrArg (fun f ↦ f z)
    (zeroInitialMobiusPolygonMap_original_overlap W ha k b3 b4 b6 r hr I hI hrI h3 hbot)
  have hy := (zeroInitialMobiusPolygonMap W ha k true).isOpenEmbedding.injective
    (he.symm.trans h)
  have hg := congrArg (fun f ↦ f z)
    (polynomialNodeOverlapOpposite_global W 0 b3 b4 b6 r hr I hI hrI h3)
  change polynomialOppositeNodeChart W 0 b3 b4 b6 r hr I hI hrI h3
    (polynomialNodeOverlapOpposite W 0 b3 b4 b6 r hr I hI hrI h3 z) = _ at hg
  exact hg.symm.trans
    (congrArg (polynomialOppositeNodeChart W 0 b3 b4 b6 r hr I hI hrI h3) hy)

end FLT.Mazur.WeierstrassDividedDepth
