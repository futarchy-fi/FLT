/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassInfinitesimalFactorization

/-!
# Torsion rigidity across square-zero quotients

Prime-to-characteristic torsion points of the actual Weierstrass group have
unique lifts across a square-zero quotient. The proof factors the reduction
kernel through the original identity chart and uses its additive coordinate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The original group identity is the base-extended infinity chart point. -/
theorem integralGroupPoint_one_left :
    (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralCurveGroup W hΔ).X).left =
      Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := A) W).toRingHom) ≫
        integralCurveChart W 1 := by
  change Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ integralCurveZero W = _
  rw [integralCurveZero, ← Category.assoc, ← Spec.map_comp,
    chartInfinityEvaluation_base (S := A)]
  rfl

variable (I : Ideal A) (hI : I ^ 2 = ⊥)

/-- The actual quotient morphism as a map over the original coefficient base. -/
def squareZeroQuotientTestMap :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ I)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl)

include hI

/-- A killed point reducing to the identity across a square-zero quotient is the identity. -/
theorem squareZero_torsion_kernel (n : ℕ) (hn : IsUnit (n : A))
    (p : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralCurveGroup W hΔ).X)
    (hp : p ^ n = 1) (hred : squareZeroQuotientTestMap I ≫ p = 1) : p = 1 := by
  have hr := congrArg Over.Hom.left hred
  rw [integralGroupPoint_one_left] at hr
  obtain ⟨x, hx⟩ := exists_infinitesimal_chart_parameter W I hI p.left p.w hr
  have hx' : infinitesimalGroupPoint W hΔ I hI x = p := Over.OverMorphism.ext hx
  have hz : x = 0 := infinitesimalGroupPoint_torsion W hΔ I hI n hn x (hx'.symm ▸ hp)
  rw [← hx', hz]
  exact congrArg Additive.toMul (infinitesimalGroupPointAddHom W hΔ I hI).map_zero

/-- Two torsion lifts with the same square-zero reduction coincide in the original group. -/
theorem squareZero_torsion_injective (n : ℕ) (hn : IsUnit (n : A))
    (p q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralCurveGroup W hΔ).X)
    (hp : p ^ n = 1) (hq : q ^ n = 1)
    (hred : squareZeroQuotientTestMap I ≫ p = squareZeroQuotientTestMap I ≫ q) : p = q := by
  let ρ : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralCurveGroup W hΔ).X) →*
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (A ⧸ I)))) ⟶
        (integralCurveGroup W hΔ).X) :=
    { toFun := fun p ↦ squareZeroQuotientTestMap I ≫ p
      map_one' := MonObj.comp_one _
      map_mul' := MonObj.comp_mul _ }
  apply div_eq_one.mp
  apply squareZero_torsion_kernel W hΔ I hI n hn (p / q)
  · rw [div_pow, hp, hq, div_self']
  · change ρ (p / q) = 1
    rw [map_div]
    change (squareZeroQuotientTestMap I ≫ p) / (squareZeroQuotientTestMap I ≫ q) = 1
    rw [hred, div_self']

end FLT.Mazur.WeierstrassIntegralChart
