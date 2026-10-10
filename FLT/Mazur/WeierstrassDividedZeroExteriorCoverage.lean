/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroExteriorOriented
public import FLT.Mazur.WeierstrassDividedInitialZeroLaurent

/-!
# Coverage and absence of extra identifications on the start-zero exterior

The original incidence and infinity charts are glued only along their proved
intersection. The resulting exterior embeds on points, and it and the retained
conic exhaust exactly the union of the first retained chart and infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
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
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "g" => olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial a)
local notation "t" => olderGlobalZeroSlopeToInfinity hπ data D j hj r hr hk0 hk
local notation "i" => finiteInfinityTensorChart hπ data K (j + 1 + r) hr
local notation "L" => olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk
local notation "E" => zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hk
local notation "C" => olderGlobalZeroConic hπ data D j hj r hr hk0 hk

/-- The retained slope uses the identical original initial tensor infinity transition. -/
theorem zeroRetainedSlopeToInfinity_eq_initial :
    t = initialZeroToTensorInfinity hπ data D (by omega) (by omega) (j + 1 + r) hr := by
  apply (cancel_mono (WeierstrassIntegralChart.infinityResidueIso D (by omega)).inv).mp
  rw [zeroRetainedSlopeToInfinity_canonical, initialZeroToTensorInfinity_laurent]

/-- The whole retained slope chart is the original initial slope chart in the global model. -/
theorem zeroRetainedSlopeChart_eq_initial :
    olderGlobalZeroSlopeChart hπ data D j hj r hr hk0 hk =
      initialZeroSlopeChart hπ data D (by omega) (by omega) (j + 1 + r) hr := by
  rw [← olderGlobalZeroSlopeToInfinity_comp, zeroRetainedSlopeToInfinity_eq_initial,
    initialZeroToTensorInfinity_chart]

/-- The exterior Laurent chart is exactly the whole original global Laurent chart. -/
@[reassoc] theorem zeroRetainedExteriorLaurentChart_toGlobal :
    zeroRetainedExteriorLaurentChart hπ data D j hj r hr hk0 hk ≫ E =
      initialZeroLaurentChart hπ data D (by omega) (j + 1 + r) hr := by
  rw [zeroRetainedExteriorLaurentChart, Category.assoc, zeroRetainedExteriorToGlobal_infinity]
  rfl

/-- The actual exterior gluing identifies no additional points in the global model. -/
theorem zeroRetainedExteriorToGlobal_injective : Function.Injective E := by
  have hL : Function.Injective L :=
    (g).isOpenEmbedding.injective.comp (fiberIncidenceImmersion a c).isClosedEmbedding.injective
  have H := (zeroRetainedIncidenceInfinity_isPullback hπ data D j hj r hr hk0 hk).flip
  intro x y hxy
  rcases SchemeOpenPushout.charts_cover s t x with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;>
    rcases SchemeOpenPushout.charts_cover s t y with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · change E (zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk v) =
      E (zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk w) at hxy
    simp only [← Scheme.Hom.comp_apply, zeroRetainedExteriorToGlobal_affine] at hxy
    exact congrArg _ (hL hxy)
  · change E (zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk v) =
      E (zeroRetainedExteriorInfinityChart hπ data D j hj r hr hk0 hk w) at hxy
    simp only [← Scheme.Hom.comp_apply, zeroRetainedExteriorToGlobal_affine,
      zeroRetainedExteriorToGlobal_infinity] at hxy
    obtain ⟨o, ho, hw⟩ := Scheme.exists_preimage_of_isPullback H v w hxy
    exact (SchemeOpenPushout.inl_eq_inr_iff s t v w).mpr ⟨o, ho, hw⟩
  · change E (zeroRetainedExteriorInfinityChart hπ data D j hj r hr hk0 hk v) =
      E (zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk w) at hxy
    simp only [← Scheme.Hom.comp_apply, zeroRetainedExteriorToGlobal_affine,
      zeroRetainedExteriorToGlobal_infinity] at hxy
    obtain ⟨o, ho, hw⟩ := Scheme.exists_preimage_of_isPullback H w v hxy.symm
    exact ((SchemeOpenPushout.inl_eq_inr_iff s t w v).mpr ⟨o, ho, hw⟩).symm
  · change E (zeroRetainedExteriorInfinityChart hπ data D j hj r hr hk0 hk v) =
      E (zeroRetainedExteriorInfinityChart hπ data D j hj r hr hk0 hk w) at hxy
    simp only [← Scheme.Hom.comp_apply, zeroRetainedExteriorToGlobal_infinity] at hxy
    exact congrArg _ ((i).isOpenEmbedding.injective hxy)

/-- The normalized projective exterior also identifies no additional global points. -/
theorem zeroRetainedOrientedToGlobal_injective :
    Function.Injective (zeroRetainedOrientedToGlobal hπ data D j hj r hr hk0 hk) :=
  (zeroRetainedExteriorToGlobal_injective hπ data D j hj r hr hk0 hk).comp
    (zeroRetainedExteriorOrientedIso hπ data D j hj r hr hk0 hk).inv.homeomorph.injective

/-- The actual exterior and conic exhaust the entire first retained chart and infinity. -/
theorem zeroRetainedExterior_conic_cover :
    Set.range E ∪ Set.range C =
      Set.range (olderGlobalTensorChart hπ data K j hj r hr) ∪ Set.range i := by
  rw [zeroRetainedExteriorToGlobal_range,
    ← olderGlobalZeroComponents_cover hπ data D j hj r hr hk0 hk]
  exact Set.union_right_comm _ _ _

/-- The complete original conic parameters together with the exterior give the same coverage. -/
theorem zeroRetainedExterior_parameters_cover :
    Set.range E ∪
      (Set.range (olderGlobalZeroConicFirstParameter hπ data D j hj r hr hk0 hk) ∪
        Set.range (olderGlobalZeroConicSecondParameter hπ data D j hj r hr hk0 hk)) =
      Set.range (olderGlobalTensorChart hπ data K j hj r hr) ∪ Set.range i := by
  rw [olderGlobalZeroConicParameters_cover, zeroRetainedExterior_conic_cover]

end FLT.Mazur.WeierstrassDividedDepth
