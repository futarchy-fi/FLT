/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineActionPoints

/-!
# Associativity of universal projective-line scaling

Compare the two action composites on both charts over the tensor product of
two independent Laurent parameter rings, using the actual product associator.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped Polynomial LaurentPolynomial TensorProduct
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ProjectiveLineActionAssociativity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open ProjectiveLineProductCharts ProjectiveLineUniversalAction ProjectiveLineActionPoints
variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]
theorem assoc_at (a c : Aˣ) (x : A) (b : Bool)
    (f : Spec (.of A) ⟶ ((MultiplicativeGroupScheme.gm K ⊗
      MultiplicativeGroupScheme.gm K) ⊗ PolygonPinching.component K).left)
    (hf : f ≫ pullback.fst _ _ ≫ pullback.fst _ _ = groupPoint K A a)
    (hg : f ≫ pullback.fst _ _ ≫ pullback.snd _ _ = groupPoint K A c)
    (hs : f ≫ pullback.snd _ _ = chartPoint K A x b) :
    f ≫ (μ[MultiplicativeGroupScheme.gm K] ▷ PolygonPinching.component K).left ≫ action K =
      f ≫ (α_ (MultiplicativeGroupScheme.gm K) (MultiplicativeGroupScheme.gm K)
        (PolygonPinching.component K)).hom.left ≫
        (MultiplicativeGroupScheme.gm K ◁ act K).left ≫ action K := by
  have hl := chart_action K A (a * c) x b
    (f ≫ (μ[MultiplicativeGroupScheme.gm K] ▷ PolygonPinching.component K).left)
    (by simp only [Category.assoc]; erw [Over.whiskerRight_left_fst]
        exact groupPoint_mul K A a c (f ≫ pullback.fst _ _) (by simpa using hf) (by simpa using hg))
    (by simp only [Category.assoc]; erw [Over.whiskerRight_left_snd]; exact hs)
  have hi := chart_action K A c x b
    (f ≫ (α_ (MultiplicativeGroupScheme.gm K) (MultiplicativeGroupScheme.gm K)
      (PolygonPinching.component K)).hom.left ≫ pullback.snd _ _)
    (by simp only [Category.assoc]; erw [Over.associator_hom_left_snd_fst]; exact hg)
    (by simp only [Category.assoc]; erw [Over.associator_hom_left_snd_snd]; exact hs)
  have hr := chart_action K A a ((if b then ↑c⁻¹ else ↑c) * x) b
    (f ≫ (α_ (MultiplicativeGroupScheme.gm K) (MultiplicativeGroupScheme.gm K)
      (PolygonPinching.component K)).hom.left ≫
      (MultiplicativeGroupScheme.gm K ◁ act K).left)
    (by simp only [Category.assoc]; erw [Over.whiskerLeft_left_fst
          (R := MultiplicativeGroupScheme.gm K) (act K),
          Over.associator_hom_left_fst (MultiplicativeGroupScheme.gm K)
            (MultiplicativeGroupScheme.gm K) (PolygonPinching.component K)]; exact hf)
    (by simp only [Category.assoc]
        erw [Over.whiskerLeft_left_snd (R := MultiplicativeGroupScheme.gm K) (act K)]
        simpa only [Category.assoc, act, Over.homMk_left] using hi)
  simp only [Category.assoc] at hl hr
  rw [hl, hr]
  cases b <;> simp [mul_comm, mul_left_comm]
/-- The coordinate ring of two independent multiplicative parameters. -/
abbrev pairRing := parameter K ⊗[K] parameter K

/-- Identify the actual group product with the spectrum of the tensor product. -/
def pairIso : (MultiplicativeGroupScheme.gm K ⊗ MultiplicativeGroupScheme.gm K) ≅
    Over.mk (parameterToBase K (pairRing K)) :=
  Over.isoMk (pullbackSpecIso K (parameter K) (parameter K))
    (pullbackSpecIso_hom_base K (parameter K) (parameter K))

/-- A polynomial chart of the actual iterated product. -/
def tripleChart (b : Bool) : Spec (.of (pairRing K)[X]) ⟶
    ((MultiplicativeGroupScheme.gm K ⊗ MultiplicativeGroupScheme.gm K) ⊗
      PolygonPinching.component K).left :=
  productChartMap K (pairRing K) b ≫ ((pairIso K).inv ▷ PolygonPinching.component K).left

/-- The first Laurent parameter in the polynomial chart. -/
def firstParameter : parameter K →ₐ[K] (pairRing K)[X] :=
  (Polynomial.CAlgHom (R := K) (A := pairRing K)).comp Algebra.TensorProduct.includeLeft

/-- The second Laurent parameter in the polynomial chart. -/
def secondParameter : parameter K →ₐ[K] (pairRing K)[X] :=
  (Polynomial.CAlgHom (R := K) (A := pairRing K)).comp Algebra.TensorProduct.includeRight

@[reassoc] theorem tripleChart_fst_fst (b : Bool) :
    tripleChart K b ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      groupPoint K (pairRing K)[X] (LaurentUnitPoints.pointUnit (firstParameter K)) := by
  rw [tripleChart, Category.assoc, Over.whiskerRight_left_fst_assoc]
  change productChartMap K (pairRing K) b ≫ pullback.fst _ _ ≫
    (pullbackSpecIso K (parameter K) (parameter K)).inv ≫ pullback.fst _ _ = _
  erw [pullbackSpecIso_inv_fst K (parameter K) (parameter K)]
  rw [← Category.assoc, productChartMap_fst, ← Spec.map_comp, groupPoint_pointUnit]
  rfl

@[reassoc] theorem tripleChart_fst_snd (b : Bool) :
    tripleChart K b ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      groupPoint K (pairRing K)[X] (LaurentUnitPoints.pointUnit (secondParameter K)) := by
  rw [tripleChart, Category.assoc, Over.whiskerRight_left_fst_assoc]
  change productChartMap K (pairRing K) b ≫ pullback.fst _ _ ≫
    (pullbackSpecIso K (parameter K) (parameter K)).inv ≫ pullback.snd _ _ = _
  erw [pullbackSpecIso_inv_snd K (parameter K) (parameter K)]
  rw [← Category.assoc, productChartMap_fst, ← Spec.map_comp, groupPoint_pointUnit]
  rfl

@[reassoc] theorem tripleChart_snd (b : Bool) :
    tripleChart K b ≫ pullback.snd _ _ = chartPoint K (pairRing K)[X] Polynomial.X b := by
  rw [tripleChart, Category.assoc, Over.whiskerRight_left_snd]
  change productChartMap K (pairRing K) b ≫ pullback.snd _ _ = _
  rw [productChartMap_snd]
  unfold chartPoint
  congr 1

theorem tripleChart_hom_ext {Y : Scheme.{u}}
    {f g : ((MultiplicativeGroupScheme.gm K ⊗ MultiplicativeGroupScheme.gm K) ⊗
      PolygonPinching.component K).left ⟶ Y}
    (h : ∀ b, tripleChart K b ≫ f = tripleChart K b ≫ g) : f = g := by
  have : IsIso ((pairIso K).inv ▷ PolygonPinching.component K).left := by
    change IsIso ((Over.forget _).map ((pairIso K).inv ▷ PolygonPinching.component K))
    infer_instance
  apply (cancel_epi ((pairIso K).inv ▷ PolygonPinching.component K).left).mp
  apply (productChartCover K (pairRing K)).hom_ext
  intro b
  exact (Category.assoc _ _ _).symm.trans ((h b).trans (Category.assoc _ _ _))

theorem assoc_act :
    μ[MultiplicativeGroupScheme.gm K] ▷ PolygonPinching.component K ≫ act K =
      (α_ (MultiplicativeGroupScheme.gm K) (MultiplicativeGroupScheme.gm K)
        (PolygonPinching.component K)).hom ≫
        MultiplicativeGroupScheme.gm K ◁ act K ≫ act K := by
  apply Over.OverMorphism.ext
  apply tripleChart_hom_ext K
  intro b
  change tripleChart K b ≫
    (μ[MultiplicativeGroupScheme.gm K] ▷ PolygonPinching.component K).left ≫ action K =
    tripleChart K b ≫ (α_ (MultiplicativeGroupScheme.gm K) (MultiplicativeGroupScheme.gm K)
      (PolygonPinching.component K)).hom.left ≫
      (MultiplicativeGroupScheme.gm K ◁ act K).left ≫ action K
  apply assoc_at K (pairRing K)[X]
    (LaurentUnitPoints.pointUnit (firstParameter K))
    (LaurentUnitPoints.pointUnit (secondParameter K)) Polynomial.X b (tripleChart K b)
  · exact tripleChart_fst_fst K b
  · exact tripleChart_fst_snd K b
  · exact tripleChart_snd K b
end FLT.Mazur.ProjectiveLineActionAssociativity
