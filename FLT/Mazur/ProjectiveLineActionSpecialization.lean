/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPinchingDiagram
public import FLT.Mazur.PolygonScalingNaturality
public import FLT.Mazur.ProjectiveLineScaling
public import FLT.Mazur.ProjectiveLineUniversalAction

/-!
# Specializing universal projective-line scaling

Constant unit parameters recover the existing scaling automorphisms.
The Hopf counit is evaluation at one, which gives the monoidal unit law.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped LaurentPolynomial Polynomial
universe u
namespace FLT.Mazur.ProjectiveLineActionSpecialization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type u) [Field K]
open ProjectiveLineProductCharts ProjectiveLineUniversalAction

/-- The point of the multiplicative group defined by a coefficient unit. -/
def unitPoint (a : Kˣ) : Spec (.of K) ⟶ Spec (.of (parameter K)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id K) a))
@[reassoc (attr := simp)] theorem unitPoint_base (a : Kˣ) :
    unitPoint K a ≫ parameterToBase K (parameter K) = 𝟙 _ := by
  rw [unitPoint, parameterToBase, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext r
  simp

/-- Insert a constant unit into the parameter factor. -/
def specialize (a : Kˣ) : ProjectiveLine.scheme K ⟶ product K (parameter K) :=
  pullback.lift (ProjectiveLine.toBase K ≫ unitPoint K a) (𝟙 _) (by simp)
@[reassoc] theorem chart_specialize (a : Kˣ) (b : Bool) :
    (chartCover K).f b ≫ specialize K a =
      Spec.map (CommRingCat.ofHom (PolygonUniversalScaling.specialize a)) ≫
        productChartMap K (parameter K) b := by
  change (if b then ProjectiveLine.right K else ProjectiveLine.left K) ≫ specialize K a = _
  apply pullback.hom_ext
  · simp only [Category.assoc, specialize, pullback.lift_fst, productChartMap_fst,
      ]
    rw [← Category.assoc]
    have hb : (if b then ProjectiveLine.right K else ProjectiveLine.left K) ≫
        ProjectiveLine.toBase K = ProjectiveLine.chartToBase K := by cases b <;> simp
    rw [hb]
    rw [unitPoint, ProjectiveLine.chartToBase, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change Polynomial.C (LaurentPolynomial.eval₂ (RingHom.id K) a r) =
      Polynomial.map (LaurentPolynomial.eval₂ (RingHom.id K) a) (Polynomial.C r)
    simp
  · simp only [Category.assoc, specialize, pullback.lift_snd, Category.comp_id,
      productChartMap_snd]
    rw [← Category.assoc, ← Spec.map_comp]
    have he : (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K (parameter K)))) ≫
        CommRingCat.ofHom (PolygonUniversalScaling.specialize a) = 𝟙 (CommRingCat.of K[X]) := by
      ext <;> simp [PolygonUniversalScaling.specialize]
    rw [he, Spec.map_id, Category.id_comp]
    cases b <;> rfl

theorem specialize_action (a : Kˣ) :
    specialize K a ≫ action K = ProjectiveLine.scaling K a := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ (specialize K a ≫ action K) =
      ProjectiveLine.left K ≫ ProjectiveLine.scaling K a
    have hc := chart_specialize K a false
    change ProjectiveLine.left K ≫ specialize K a = _ at hc
    rw [← Category.assoc, hc, Category.assoc, left_action, ProjectiveLine.left_scaling]
    rw [← Category.assoc]
    congr 1
    simpa only [leftMap, ProjectiveLine.chartScaling, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      using congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
        (PolygonUniversalScaling.specialize_left a)
  · change ProjectiveLine.right K ≫ (specialize K a ≫ action K) =
      ProjectiveLine.right K ≫ ProjectiveLine.scaling K a
    have hc := chart_specialize K a true
    change ProjectiveLine.right K ≫ specialize K a = _ at hc
    rw [← Category.assoc, hc, Category.assoc, right_action, ProjectiveLine.right_scaling]
    rw [← Category.assoc]
    congr 1
    simpa only [rightMap, ProjectiveLine.chartScaling, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      using congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
        (PolygonUniversalScaling.specialize_right a)
theorem identity_left : η[MultiplicativeGroupScheme.gm K].left = unitPoint K 1 := by
  change Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom K (parameter K)).toRingHom) = _
  unfold unitPoint
  congr 1
  apply CommRingCat.hom_ext
  apply PolygonScalingNaturality.ringHom_ext
  · intro r
    change Coalgebra.counit (R := K) (LaurentPolynomial.C r) = _
    simp
  · change Coalgebra.counit (R := K) (LaurentPolynomial.T 1 : LaurentPolynomial K) = _
    simp
  · change Coalgebra.counit (R := K) (LaurentPolynomial.T (-1) : LaurentPolynomial K) = _
    simp

theorem unit_act : η[MultiplicativeGroupScheme.gm K] ▷ PolygonPinching.component K ≫ act K =
    (λ_ (PolygonPinching.component K)).hom := by
  apply (cancel_epi (λ_ (PolygonPinching.component K)).inv).mp
  apply Over.OverMorphism.ext
  change ((λ_ (PolygonPinching.component K)).inv.left ≫
      (η[MultiplicativeGroupScheme.gm K] ▷ PolygonPinching.component K).left) ≫ action K = _
  have he : (λ_ (PolygonPinching.component K)).inv.left ≫
      (η[MultiplicativeGroupScheme.gm K] ▷ PolygonPinching.component K).left =
      specialize K 1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, Over.whiskerRight_left_fst]
      simp only [Over.tensorUnit_hom]
      rw [Over.leftUnitor_inv_left_fst_assoc (PolygonPinching.component K), identity_left]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Over.whiskerRight_left_snd]
      simp only [Over.tensorUnit_hom]
      rw [Over.leftUnitor_inv_left_snd (PolygonPinching.component K)]
      exact (pullback.lift_snd _ _ _).symm
  rw [he, specialize_action, ProjectiveLine.scaling_one]
  change _ = ((λ_ (PolygonPinching.component K)).inv ≫ (λ_ _).hom).left
  simp
end FLT.Mazur.ProjectiveLineActionSpecialization
