/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedLineProjection
import all FLT.Mazur.WeierstrassCoefficientShearRetainedLineProjection
public import FLT.Mazur.WeierstrassCoefficientShearSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Actual retained lines under coefficient specialization

The complete original line embeddings commute with the polynomial coefficient
map when the actual unsheared slope specializes. The two signed root lines
therefore retain their affine parameters, including their node origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (f : S →ₐ[R] T) (r : S) (t : T)
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ) (hm : j + 1 + m ≤ n)
  (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, by omega⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, by omega⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (gs : algebraMap R T (π ^ (start + j)) = 0) (gp : algebraMap R T π = 0)
  (g3 : algebraMap R T (data ⟨j + 1, by omega⟩).b3 = 0)
  (g4 : algebraMap R T (data ⟨j + 1, by omega⟩).b4 = 0)
  (gt : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
local notation "US" => rootShearCurve (W.map (algebraMap R S)) r
local notation "UT" => rootShearCurve (W.map (algebraMap R T)) t
local notation "LS" => coefficientShearRetainedLine hπ data S r (j + 1 + m) hm
  ⟨j, by omega⟩ hs hp h3 h4 hr
local notation "LT" => coefficientShearRetainedLine hπ data T t (j + 1 + m) hm
  ⟨j, by omega⟩ gs gp g3 g4 gt
local notation "M" => coefficientShearSpecialization hπ data S T r t (j + 1 + m) hm f
local notation "p" => Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f.toRingHom))

/-- The actual complete retained line specializes with every original slope function preserved. -/
@[reassoc] theorem coefficientShearSpecialization_retainedLine
    (v : S) (w : T) (hv : v * (v + (US).a₁) = 0)
    (hw : w * (w + (UT).a₁) = 0) (hvw : f (v + r) = w + t) :
    LT w hw ≫ M = p ≫ LS v hv := by
  symm
  apply coefficientShearSpecialization_unique
  · rw [Category.assoc, coefficientShearRetainedLine_structure,
      ← Category.assoc (LT w hw), coefficientShearRetainedLine_structure]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun _ => Polynomial.map_C f.toRingHom)
  · rw [Category.assoc,
      coefficientShearRetainedLine_projection hπ data S r j hj m hm,
      coefficientShearRetainedLine_projection hπ data T t j hj m hm]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 1
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      (originalShearLineMap_coefficient W (π ^ (start + j)) π
        (data ⟨j + 1, by omega⟩).b3 (data ⟨j + 1, by omega⟩).b4
        (data ⟨j + 1, by omega⟩).b6 S r hs hp h3 h4 hr v hv
        T f t w gs gp g3 g4 gt hw hvw)

/-- The first retained line specializes with the same full affine coordinate. -/
@[reassoc] theorem coefficientShearSpecialization_retainedFirst (hrt : f r = t) :
    LT 0 (middle_first_root UT) ≫ M = p ≫ LS 0 (middle_first_root US) := by
  apply coefficientShearSpecialization_retainedLine hπ data S T f r t j hj m hm
  simpa only [zero_add] using hrt

/-- The signed second retained line specializes with its original full affine coordinate. -/
@[reassoc] theorem coefficientShearSpecialization_retainedSecond (hrt : f r = t) :
    LT (-(UT).a₁) (middle_second_root UT) ≫ M =
      p ≫ LS (-(US).a₁) (middle_second_root US) := by
  apply coefficientShearSpecialization_retainedLine hπ data S T f r t j hj m hm
  rw [(rootShearCurve_coefficients (W := W.map (algebraMap R S)) r).1,
    (rootShearCurve_coefficients (W := W.map (algebraMap R T)) t).1]
  change f (-(algebraMap R S W.a₁ + 2 * r) + r) =
    -(algebraMap R T W.a₁ + 2 * t) + t
  simp only [map_add, map_neg, map_mul, map_ofNat, f.commutes, hrt]

end FLT.Mazur.WeierstrassDividedDepth
