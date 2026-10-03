/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSpaceReindex
public import FLT.Mazur.ProjectiveLineCharts
public import FLT.Mazur.ProjectiveProductChartOverlaps
/-!
# Polynomial charts on the standard projective line

The two homogeneous charts of Proj K[X₀,X₁] are identified with K[X]. The
coordinates are X₁/X₀ and X₀/X₁ respectively. Their embeddings cover Proj
and preserve the original coefficient projection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial
universe u
namespace FLT.Mazur.ProjectiveLineStandardCharts
open ProjectiveSpace
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Interchange the two homogeneous coordinates. -/
abbrev swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

theorem swap_scalar (i : Fin 2) (r : K) :
    reindexChartRingMap K (swap) i (chartScalars K (Fin 2) i r) =
      chartScalars K (Fin 2) ((swap).symm i) r := by
  apply HomogeneousLocalization.val_injective
  simp [reindexChartRingMap, chartScalars, constantsToZero,
    HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.map_mk]

/-- Swap the homogeneous coordinates from chart one to chart zero. -/
def swapMap10 : chartRing K (Fin 2) 1 →+* chartRing K (Fin 2) 0 :=
  reindexChartRingMap K swap 1

/-- Swap the homogeneous coordinates from chart zero to chart one. -/
def swapMap01 : chartRing K (Fin 2) 0 →+* chartRing K (Fin 2) 1 :=
  reindexChartRingMap K swap 0

@[simp] theorem swapMap10_scalar (r : K) :
    swapMap10 K (chartScalars K (Fin 2) 1 r) = chartScalars K (Fin 2) 0 r :=
  swap_scalar K 1 r
@[simp] theorem swapMap01_scalar (r : K) :
    swapMap01 K (chartScalars K (Fin 2) 0 r) = chartScalars K (Fin 2) 1 r :=
  swap_scalar K 0 r
@[simp] theorem swapMap10_coordinate :
    swapMap10 K (coordinate K (Fin 2) 1 0) = coordinate K (Fin 2) 0 1 :=
  reindexChartRingMap_coordinate K swap 1 0
@[simp] theorem swapMap01_coordinate :
    swapMap01 K (coordinate K (Fin 2) 0 1) = coordinate K (Fin 2) 1 0 :=
  reindexChartRingMap_coordinate K swap 0 1

theorem swap_comp10 : (swapMap01 K).comp (swapMap10 K) = RingHom.id _ := by
  apply chartRing_hom_ext
  · intro r; simp
  · intro i; fin_cases i <;> simp

theorem swap_comp01 : (swapMap10 K).comp (swapMap01 K) = RingHom.id _ := by
  apply chartRing_hom_ext
  · intro r; simp
  · intro i; fin_cases i <;> simp

/-- Swapping homogeneous coordinates identifies the two chart rings. -/
def swapRingEquiv : chartRing K (Fin 2) 1 ≃+* chartRing K (Fin 2) 0 where
  __ := swapMap10 K
  invFun := swapMap01 K
  left_inv := RingHom.congr_fun (swap_comp10 K)
  right_inv := RingHom.congr_fun (swap_comp01 K)

/-- Polynomial coordinates X₁/X₀ on the zeroth homogeneous chart. -/
def leftRingEquiv : chartRing K (Fin 2) 0 ≃ₐ[K] K[X] :=
  (chartPolynomialEquiv K 1).symm.trans (MvPolynomial.uniqueAlgEquiv K (Fin 1))

/-- Polynomial coordinates X₀/X₁ on the first homogeneous chart. -/
def rightRingEquiv : chartRing K (Fin 2) 1 ≃+* K[X] :=
  (swapRingEquiv K).trans (leftRingEquiv K).toRingEquiv

@[simp] theorem leftRingEquiv_scalar (r : K) :
    leftRingEquiv K (chartScalars K (Fin 2) 0 r) = Polynomial.C r :=
  (leftRingEquiv K).commutes r

@[simp] theorem rightRingEquiv_scalar (r : K) :
    rightRingEquiv K (chartScalars K (Fin 2) 1 r) = Polynomial.C r := by
  change leftRingEquiv K (swapMap10 K (chartScalars K (Fin 2) 1 r)) = Polynomial.C r
  rw [swapMap10_scalar, leftRingEquiv_scalar]

@[simp] theorem leftRingEquiv_coordinate :
    leftRingEquiv K (coordinate K (Fin 2) 0 1) = Polynomial.X := by
  change MvPolynomial.uniqueAlgEquiv K (Fin 1)
    (chartToPolynomial K 1 (coordinate K (Fin 2) 0 (Fin.succ 0))) = _
  rw [chartToPolynomial_coordinate]
  simp

@[simp] theorem rightRingEquiv_coordinate :
    rightRingEquiv K (coordinate K (Fin 2) 1 0) = Polynomial.X := by
  change leftRingEquiv K (swapMap10 K (coordinate K (Fin 2) 1 0)) = _
  rw [swapMap10_coordinate]
  exact leftRingEquiv_coordinate K

/-- The spectrum isomorphism for the zeroth chart. -/
def leftSpecIso : ProjectiveLine.chart K ≅ Spec (.of (chartRing K (Fin 2) 0)) :=
  Scheme.Spec.mapIso (leftRingEquiv K).toRingEquiv.toCommRingCatIso.op

/-- The spectrum isomorphism for the first chart. -/
def rightSpecIso : ProjectiveLine.chart K ≅ Spec (.of (chartRing K (Fin 2) 1)) :=
  Scheme.Spec.mapIso (rightRingEquiv K).toCommRingCatIso.op

/-- The affine chart with coordinate X₁/X₀. -/
def left : ProjectiveLine.chart K ⟶ space K (Fin 2) :=
  (leftSpecIso K).hom ≫ chartMap K (Fin 2) 0

/-- The affine chart with coordinate X₀/X₁. -/
def right : ProjectiveLine.chart K ⟶ space K (Fin 2) :=
  (rightSpecIso K).hom ≫ chartMap K (Fin 2) 1

instance left_isOpenImmersion : IsOpenImmersion (left K) := by unfold left; infer_instance
instance right_isOpenImmersion : IsOpenImmersion (right K) := by unfold right; infer_instance

theorem left_range : (left K).opensRange = chart K (Fin 2) 0 := by
  change ((leftSpecIso K).hom ≫ chartMap K (Fin 2) 0).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (chart K (Fin 2) 0).opensRange_ι

theorem right_range : (right K).opensRange = chart K (Fin 2) 1 := by
  change ((rightSpecIso K).hom ≫ chartMap K (Fin 2) 1).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (chart K (Fin 2) 1).opensRange_ι

theorem covers (x : space K (Fin 2)) :
    x ∈ Set.range (left K) ∨ x ∈ Set.range (right K) := by
  obtain ⟨i, hi⟩ := exists_mem_chart K (Fin 2) x
  fin_cases i
  · left; change x ∈ (left K).opensRange; rwa [left_range]
  · right; change x ∈ (right K).opensRange; rwa [right_range]

@[reassoc] theorem left_base : left K ≫ baseProjection K (Fin 2) =
    ProjectiveLine.chartToBase K := by
  rw [left, Category.assoc, chartMap_baseProjection]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact leftRingEquiv_scalar K r

@[reassoc] theorem right_base : right K ≫ baseProjection K (Fin 2) =
    ProjectiveLine.chartToBase K := by
  rw [right, Category.assoc, chartMap_baseProjection]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact rightRingEquiv_scalar K r
end FLT.Mazur.ProjectiveLineStandardCharts
