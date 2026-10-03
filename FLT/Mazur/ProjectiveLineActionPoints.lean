/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentUnitPoints
public import FLT.Mazur.ProjectiveLineActionSpecialization

/-!
# Universal action on affine algebra points

Both projective charts scale an arbitrary algebra-valued coordinate by a unit
or its inverse. The actual Hopf multiplication multiplies those units.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped Polynomial LaurentPolynomial TensorProduct
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ProjectiveLineActionPoints
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open ProjectiveLineProductCharts ProjectiveLineUniversalAction
variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]
/-- The multiplicative-group point represented by a unit of the coefficient algebra. -/
def groupPoint (a : Aˣ) : Spec (.of A) ⟶ (MultiplicativeGroupScheme.gm K).left :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := K) a).toRingHom)
/-- An algebra-valued coordinate in either projective-line chart. -/
def chartPoint (x : A) (b : Bool) : Spec (.of A) ⟶ ProjectiveLine.scheme K :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap K A) x)) ≫
    (chartCover K).f b
@[reassoc] theorem groupPoint_base (a : Aˣ) :
    groupPoint K A a ≫ (MultiplicativeGroupScheme.gm K).hom = parameterToBase K A := by
  rw [groupPoint]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp [LaurentUnitPoints.evalUnit]
@[reassoc (attr := simp)] theorem chartPoint_base (x : A) (b : Bool) :
    chartPoint K A x b ≫ ProjectiveLine.toBase K = parameterToBase K A := by
  rw [chartPoint, Category.assoc, chartCover_toBase]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp

theorem chart_action (a : Aˣ) (x : A) (b : Bool)
    (f : Spec (.of A) ⟶ product K (parameter K))
    (hf : f ≫ pullback.fst _ _ = groupPoint K A a)
    (hs : f ≫ pullback.snd _ _ = chartPoint K A x b) :
    f ≫ action K = chartPoint K A ((if b then ↑a⁻¹ else ↑a) * x) b := by
  let e : (parameter K)[X] →+* A :=
    Polynomial.eval₂RingHom (LaurentUnitPoints.evalUnit (R := K) a).toRingHom x
  have he : f = Spec.map (CommRingCat.ofHom e) ≫ productChartMap K (parameter K) b := by
    apply pullback.hom_ext
    · rw [hf, Category.assoc, productChartMap_fst, ← Spec.map_comp]
      unfold groupPoint
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      simp [e]
    · rw [hs, chartPoint, Category.assoc, productChartMap_snd, ← Category.assoc, ← Spec.map_comp]
      congr 1
      congr 1
      ext <;> simp [e, LaurentUnitPoints.evalUnit]
  rw [he, Category.assoc]
  cases b
  · rw [left_action, ← Category.assoc]
    unfold chartPoint leftMap
    rw [← Spec.map_comp]
    congr 1
    congr 1
    ext <;> simp [e, PolygonUniversalScaling.scaleLeft, PolygonUniversalScaling.u,
      PolygonChartScaling.coordinateUnit, LaurentUnitPoints.evalUnit]
  · rw [right_action, ← Category.assoc]
    unfold chartPoint rightMap
    rw [← Spec.map_comp]
    congr 1
    congr 1
    ext <;> simp [e, PolygonUniversalScaling.scaleRight, PolygonUniversalScaling.u,
      PolygonChartScaling.coordinateUnit, LaurentUnitPoints.evalUnit]
theorem groupPoint_mul (a c : Aˣ)
    (f : Spec (.of A) ⟶ (MultiplicativeGroupScheme.gm K ⊗
      MultiplicativeGroupScheme.gm K).left)
    (hf : f ≫ pullback.fst _ _ = groupPoint K A a)
    (hs : f ≫ pullback.snd _ _ = groupPoint K A c) :
    f ≫ μ[MultiplicativeGroupScheme.gm K].left = groupPoint K A (a * c) := by
  let e := Algebra.TensorProduct.lift (LaurentUnitPoints.evalUnit (R := K) a)
    (LaurentUnitPoints.evalUnit (R := K) c) (fun _ _ ↦ Commute.all _ _)
  have he : f = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (pullbackSpecIso K (parameter K) (parameter K)).inv := by
    apply pullback.hom_ext
    · erw [hf, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      unfold groupPoint
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      simp [e]
    · erw [hs, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      unfold groupPoint
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      simp [e]
  rw [he, MultiplicativeGroupScheme.multiplication_left, Category.assoc,
    Iso.inv_hom_id_assoc, groupPoint, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply PolygonScalingNaturality.ringHom_ext
  · intro r
    change e ((Bialgebra.comulAlgHom K (parameter K)) (algebraMap K (parameter K) r)) = _
    simp [e, LaurentUnitPoints.evalUnit]
  · change e (Coalgebra.comul (R := K) (LaurentPolynomial.T 1)) = _
    simp [e]
  · change e (Coalgebra.comul (R := K) (LaurentPolynomial.T (-1))) = _
    simp [e, mul_comm]
theorem groupPoint_pointUnit (f : parameter K →ₐ[K] A) :
    groupPoint K A (LaurentUnitPoints.pointUnit f) = Spec.map (CommRingCat.ofHom f.toRingHom) := by
  unfold groupPoint
  rw [LaurentUnitPoints.evalUnit_pointUnit]
end FLT.Mazur.ProjectiveLineActionPoints
