/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSlopeContraction
public import FLT.Mazur.WeierstrassModificationXZeroResidueLaurent

/-!
# The actual retained start-zero attachment in Laurent coordinates

The whole original infinity attachment is T=(v+a)/v. Its image is exactly
D(T-1), with both the residue coefficients and the original cubic projection
retained. No equality after contraction is used without its cartesian lift.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "a" => residue R W.a₁
local notation "P" => SlopeOpen a
local notation "hd" => (by omega : 0 < depth)
local notation "t" => olderGlobalZeroSlopeToInfinity hπ data D j hj r hr hk0 hk
local notation "f" => zeroResidueToInfinity D hd (start + j) hk0
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "m" => zeroResidueInfinityTensorMap D hd (start + j) hk0
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "u" => Units.mk0 a
  (IsUnit.ne_zero (IsUnit.map (residue R) (SplitNodeDepth.a₁_unit D)))

/-- The original retained attachment preserves every residue coefficient. -/
@[reassoc] theorem zeroRetainedSlopeToInfinity_structure :
    t ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (K ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) =
        Spec.map (CommRingCat.ofHom (algebraMap K P)) := by
  rw [← finiteInfinityTensorChart_structure hπ data K (j + 1 + r) hr,
    zeroRetainedIncidenceInfinity_comp_assoc, zeroRetainedIncidence_structure]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1

/-- The retained attachment has the original full integral infinity projection. -/
@[reassoc] theorem zeroRetainedSlopeToInfinity_projection :
    t ≫ TensorOpenChart.projection = f := by
  apply (cancel_mono (integralCurveChart W 1)).mp
  rw [Category.assoc, ← finiteInfinityTensorChart_toCurve hπ data K (j + 1 + r) hr,
    olderGlobalZeroSlopeToInfinity_comp_assoc, zeroRetainedSlope_toCurve]
  exact (zeroResidueToInfinity_contraction D hd (start + j) hk0
    (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)).symm

/-- Both cartesian projections identify the whole retained tensor attachment. -/
theorem zeroRetainedSlopeToInfinity_eq_spec :
    t = Spec.map (CommRingCat.ofHom (m).toRingHom) := by
  apply (cancel_mono (pullbackSpecIso R K (WeierstrassIntegralChart.Coordinate W 1)).inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst']
    rw [zeroRetainedSlopeToInfinity_structure, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (fun x => (AlgHom.commutes m x).symm))
  · simp only [Category.assoc, pullbackSpecIso_inv_snd]
    change t ≫ TensorOpenChart.projection =
      Spec.map (CommRingCat.ofHom (m).toRingHom) ≫ TensorOpenChart.projection
    rw [zeroRetainedSlopeToInfinity_projection, zeroResidueInfinityTensorMap_projection]

/-- The full original retained attachment has the canonical ordered tangent ratio. -/
theorem zeroRetainedSlopeToInfinity_canonical :
    t ≫ (infinityResidueIso D hd).inv =
      Spec.map (CommRingCat.ofHom (slopeLaurentMap u).toRingHom) := by
  rw [zeroRetainedSlopeToInfinity_eq_spec, ← zeroResidueLaurentMap_spec,
    zeroResidueLaurentMap_eq]

/-- Its complete image is the original Laurent torus with one removed. -/
theorem zeroRetainedSlopeToInfinity_laurent_range :
    Set.range (t ≫ (infinityResidueIso D hd).inv) =
      (PrimeSpectrum.basicOpen (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹]) :
        Set (PrimeSpectrum K[T;T⁻¹])) := by
  rw [zeroRetainedSlopeToInfinity_canonical]
  exact slopeLaurentMap_range u

end FLT.Mazur.WeierstrassDividedDepth
