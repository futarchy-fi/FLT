/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearScaleOneConicBoundary
public import FLT.Mazur.WeierstrassSuccessiveXConicPuncturedParameters

/-!
# The actual signed conic punctures under tangent-root interchange

Both independently constructed maps are compared on all three original
tensor coordinates. Their Laurent parameters retain the original signs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r t : S)
  (hs : algebraMap R S s = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (hc : algebraMap R S b6 = 0)
local notation "Ur" => rootShearCurve (W.map (algebraMap R S)) r
local notation "Ut" => rootShearCurve (W.map (algebraMap R S)) t
local notation "c" => algebraMap R S b6
local notation "Fr" => tensorShearScaleOneConicMap W s π b3 b4 b6 S r hs hp h3 h4 hr
local notation "Ft" => tensorShearScaleOneConicMap W s π b3 b4 b6 S t hs hp h3 h4 ht

/-- The first original puncture is exactly the opposite puncture for the other chosen root. -/
theorem tensorShearScaleOneConicFirst_rootChange (hrt : r + t = -algebraMap R S W.a₁) :
    (conicPuncturedFirst Ur c hc).comp Fr = (conicPuncturedSecond Ut c hc).comp Ft := by
  have har := (rootShearCurve_coefficients (W := W.map (algebraMap R S)) r).1
  have hat := (rootShearCurve_coefficients (W := W.map (algebraMap R S)) t).1
  have he : (Ut).a₁ = -(Ur).a₁ := by
    rw [har, hat]
    change algebraMap R S W.a₁ + 2 * t = -(algebraMap R S W.a₁ + 2 * r)
    linear_combination 2 * hrt
  have hv : -(Ut).a₁ + t = r := by
    rw [hat]
    change -(algebraMap R S W.a₁ + 2 * t) + t = r
    linear_combination -hrt
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  intro i
  change conicPuncturedFirst Ur c hc (Fr (tensorCoord W s π b3 b4 b6 S i)) =
    conicPuncturedSecond Ut c hc (Ft (tensorCoord W s π b3 b4 b6 S i))
  rw [tensorShearScaleOneConicMap_coord, tensorShearScaleOneConicMap_coord]
  fin_cases i
  · change conicPuncturedFirst Ur c hc (conicT (Ur).a₁ c) =
      conicPuncturedSecond Ut c hc (conicT (Ut).a₁ c)
    simp only [conicPuncturedFirst, conicPuncturedSecond, conicEvaluation_t, he,
      map_neg, neg_neg]
  · change conicPuncturedFirst Ur c hc (conicV (Ur).a₁ c + algebraMap S _ r) =
      conicPuncturedSecond Ut c hc (conicV (Ut).a₁ c + algebraMap S _ t)
    simp only [map_add, AlgHom.commutes, conicPuncturedFirst, conicPuncturedSecond,
      conicEvaluation_v, zero_add]
    change LaurentPolynomial.C r = -LaurentPolynomial.C (Ut).a₁ + LaurentPolynomial.C t
    rw [← map_neg, ← map_add, hv]
  · change conicPuncturedFirst Ur c hc 0 = conicPuncturedSecond Ut c hc 0
    simp only [map_zero]

/-- The other original puncture becomes the first one with its signed parameter unchanged. -/
theorem tensorShearScaleOneConicSecond_rootChange (hrt : r + t = -algebraMap R S W.a₁) :
    (conicPuncturedSecond Ur c hc).comp Fr = (conicPuncturedFirst Ut c hc).comp Ft := by
  exact (tensorShearScaleOneConicFirst_rootChange W s π b3 b4 b6 S t r hs hp h3 h4
    ht hr hc (by rwa [add_comm])).symm

local notation "Ir" => tensorShearScaleOneConicImmersion W s π b3 b4 b6 S r hs hp h3 h4 hr
local notation "It" => tensorShearScaleOneConicImmersion W s π b3 b4 b6 S t hs hp h3 h4 ht

/-- Both full first/second puncture morphisms agree in the original tensor chart. -/
theorem tensorShearScaleOneConicFirst_spec_rootChange
    (hrt : r + t = -algebraMap R S W.a₁) :
    Spec.map (CommRingCat.ofHom (conicPuncturedFirst Ur c hc).toRingHom) ≫ Ir =
      Spec.map (CommRingCat.ofHom (conicPuncturedSecond Ut c hc).toRingHom) ≫ It := by
  rw [tensorShearScaleOneConicImmersion_eq_spec, tensorShearScaleOneConicImmersion_eq_spec,
    ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (tensorShearScaleOneConicFirst_rootChange W s π b3 b4 b6 S r t hs hp h3 h4 hr ht hc hrt)

/-- Both opposite/first punctures agree as complete scheme maps with unchanged signed parameter. -/
theorem tensorShearScaleOneConicSecond_spec_rootChange
    (hrt : r + t = -algebraMap R S W.a₁) :
    Spec.map (CommRingCat.ofHom (conicPuncturedSecond Ur c hc).toRingHom) ≫ Ir =
      Spec.map (CommRingCat.ofHom (conicPuncturedFirst Ut c hc).toRingHom) ≫ It := by
  rw [tensorShearScaleOneConicImmersion_eq_spec, tensorShearScaleOneConicImmersion_eq_spec,
    ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (tensorShearScaleOneConicSecond_rootChange W s π b3 b4 b6 S r t hs hp h3 h4 hr ht hc hrt)

end FLT.Mazur.WeierstrassSuccessiveX
