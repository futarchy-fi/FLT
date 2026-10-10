/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialIncidenceInfinity
public import FLT.Mazur.WeierstrassModificationXResidueSlopeLaurent

/-!
# The actual retained slope attachment has its original Laurent transition

The global attachment is identified on both its original cubic projection
and residue coefficients. The tensor pullback then identifies the whole map,
so the Laurent formula applies to the actual exterior gluing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
open WeierstrassModificationX WeierstrassIntegralChart
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "P" => SlopeOpen a
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial a)
local notation "t" => initialGlobalSlopeToInfinity hπ data D j hj hstart hk
local notation "L" => initialGlobalIncidenceLine hπ data D j hj hstart hk
local notation "i" => finiteInfinityTensorChart hπ data K j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "g" => finiteGlobalStructure hπ data j hj
local notation "f" => residueSlopeOriginalMap D start hstart hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "o" => residueSlopeOverlap D start hstart hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "m" => residueSlopeInfinityMap D start hstart hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
local notation "e" => residueSlopeInfinityTensorMap D start hstart hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The actual retained attachment preserves every original residue coefficient. -/
@[reassoc] theorem initialGlobalSlopeToInfinity_structure :
    t ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (K ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) =
        Spec.map (CommRingCat.ofHom (algebraMap K P)) := by
  rw [← finiteInfinityTensorChart_structure hπ data K j hj,
    initialGlobalSlopeToInfinity_comp_assoc, initialGlobalIncidenceLine_structure]
  rw [← Spec.map_comp]
  congr 1

/-- The entire initial slope overlap retains the original affine contraction. -/
@[reassoc] theorem initialGlobalSlope_affineContraction :
    s ≫ L ≫ pullback.snd q g ≫ finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)) ≫ integralCurveChart W 2 := by
  rw [initialGlobalIncidenceLine, initialGlobalResidueFiberChart]
  simp only [Category.assoc, globalInitialTensorChart_toCurve]
  change s ≫ fiberIncidenceImmersion a c ≫
    (residueFiberIso D start hstart hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)).hom ≫
        residueChartContraction start (Data.b3 d) (Data.b4 d) (Data.b6 d)
          (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) = _
  rw [residueFiberIso_contraction]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ _ = _
  simp only [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The actual global attachment projects to the original integral infinity transition. -/
@[reassoc] theorem initialGlobalSlopeToInfinity_projection :
    t ≫ TensorOpenChart.projection = Spec.map (CommRingCat.ofHom (AlgHom.toRingHom m)) := by
  apply (cancel_mono (integralCurveChart W 1)).mp
  rw [Category.assoc, ← finiteInfinityTensorChart_toCurve hπ data K j hj,
    initialGlobalSlopeToInfinity_comp_assoc]
  erw [initialGlobalSlope_affineContraction]
  rw [show CommRingCat.ofHom (AlgHom.toRingHom m) =
    CommRingCat.ofHom (transitionBase W 2 1).toRingHom ≫
      CommRingCat.ofHom (AlgHom.toRingHom o) from rfl]
  rw [Spec.map_comp, Category.assoc, integralCurve_output_transition, ← Category.assoc]
  congr 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun w => (residueSlopeOverlap_base D start hstart hk
    (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) w).symm)

/-- The complete global slope-to-infinity attachment is the explicit tensor transition. -/
theorem initialGlobalSlopeToInfinity_eq_spec :
    t = Spec.map (CommRingCat.ofHom (AlgHom.toRingHom e)) := by
  apply (cancel_mono (pullbackSpecIso R K (WeierstrassIntegralChart.Coordinate W 1)).inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst']
    rw [initialGlobalSlopeToInfinity_structure, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (fun r => (AlgHom.commutes e r).symm))
  · simp only [Category.assoc, pullbackSpecIso_inv_snd]
    change t ≫ TensorOpenChart.projection =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom e)) ≫ TensorOpenChart.projection
    rw [initialGlobalSlopeToInfinity_projection, residueSlopeInfinityTensorMap_projection]

/-- The actual gluing transition in the full original Laurent infinity coordinates. -/
theorem initialGlobalSlopeToInfinity_laurent (hdepth : 0 < depth) :
    t ≫ (infinityResidueIso D hdepth).inv =
      Spec.map (CommRingCat.ofHom
        (residueSlopeLaurentMap D start hstart hk
          (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
          (Data.factor6 d) hdepth).toRingHom) := by
  rw [initialGlobalSlopeToInfinity_eq_spec, residueSlopeLaurentMap_spec]

end FLT.Mazur.WeierstrassDividedDepth
