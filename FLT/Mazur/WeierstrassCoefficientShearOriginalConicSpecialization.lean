/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneConicSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneConicSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
public import FLT.Mazur.WeierstrassSuccessiveZeroConicShearPunctures
public import FLT.Mazur.WeierstrassConicPunctureCoefficient
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Coefficient specialization of the original scale-one residue conic

Compare the full independently constructed residue conic with the actual
specialized model. Its original integral immersion is retained, and the
root-zero equation transport is the only change of conic presentation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ) (hm : j + 1 + m ≤ n)
  (D : SplitNodeDepth W π depth) (hk0 : start + j = 0)
  (hk : 2 * (start + j + 1) ≤ depth)
  (h3 : residue R (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : residue R (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "c" => residue R (Data.b6 d)
local notation "hs" => show algebraMap R K (π ^ (start + j)) = 1 from by
  simp only [hk0, pow_zero, map_one]
local notation "hp" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "F" => zeroResidueConicImmersion D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "B" => coefficientShearRetainedTensorChart hπ data K 0
  (j + 1 + m) hm (Fin.mk j (by omega))
local notation "E" => conicCoefficientTransport c (rootShearZero_tangent V)
local notation "I" => Scheme.Spec.mapIso (E).toRingEquiv.toCommRingCatIso.op
variable (T : Type) [CommRing T] [Algebra R T] (f : ResidueField R →ₐ[R] T) (t : T)
  (gs : algebraMap R T (π ^ (start + j)) = 1) (gp : algebraMap R T π = 0)
  (g3 : algebraMap R T (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (g4 : algebraMap R T (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (gt : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
  (hrt : f 0 = t)
local notation "b" => (rootShearCurve (W.map (algebraMap R T)) t).a₁
local notation "cT" => algebraMap R T (Data.b6 d)
local notation "ha" => rootShearTangent_coefficient W K 0 T f t hrt
local notation "hc" => f.commutes (Data.b6 d)
local notation "p" => Spec.map (CommRingCat.ofHom
  (conicCoefficientMap f.toRingHom (U).a₁ c b cT ha hc))
local notation "CT" => coefficientShearRetainedScaleOneConic hπ data T t
  j hj m hm gs gp g3 g4 gt
local notation "CS" => coefficientShearRetainedScaleOneConic hπ data K 0
  j hj m hm hs hp h3 h4 hr
local notation "M" => coefficientShearSpecialization hπ data K T 0 t (j + 1 + m) hm f

include h3 h4 in
/-- The complete original scale-one residue conic is retained in the specialization square. -/
theorem coefficientShearSpecialization_originalResidueConic :
    CT ≫ M = p ≫ (I).inv ≫ F ≫ B := by
  rw [zeroResidueConicImmersion_eq_shear D hk0 hk d hs hp h3 h4 hr]
  change CT ≫ M = p ≫ (I).inv ≫ ((I).hom ≫ _) ≫ B
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact coefficientShearSpecialization_retainedScaleOneConic hπ data K T f 0 t
    j hj m hm hs hp h3 h4 hr gs gp g3 g4 gt hrt

variable (hcz : residue R (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hdz : algebraMap R T (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
local notation "UT" => rootShearCurve (W.map (algebraMap R T)) t
local notation "L" => Spec.map (CommRingCat.ofHom
  (WeierstrassIntegralChart.nodalLaurentCoefficientMap f.toRingHom))

include h3 h4 hrt in
/-- The actual original first conic parameter retains the entire model specialization. -/
theorem coefficientShearOriginalConicFirst_specialization :
    Spec.map (CommRingCat.ofHom (conicPuncturedFirst UT cT hdz).toRingHom) ≫ CT ≫ M =
      L ≫ Spec.map (CommRingCat.ofHom (conicPuncturedFirst V c hcz).toRingHom) ≫ F ≫ B := by
  have Hmodel := coefficientShearSpecialization_retainedScaleOneConic hπ data K T f 0 t
    j hj m hm hs hp h3 h4 hr gs gp g3 g4 gt hrt
  have Hparam := conicPuncturedFirst_spec_coefficient f.toRingHom U UT c cT ha hc hcz hdz
  have Horiginal := zeroResidueConicFirst_spec_eq_shear D hk0 hk d hs hp h3 h4 hr hcz
  calc
    _ = Spec.map (CommRingCat.ofHom (conicPuncturedFirst UT cT hdz).toRingHom) ≫ p ≫ CS :=
      congrArg (_ ≫ ·) Hmodel
    _ = L ≫ Spec.map (CommRingCat.ofHom (conicPuncturedFirst U c hcz).toRingHom) ≫ CS := by
      simpa only [Category.assoc] using congrArg (· ≫ CS) Hparam
    _ = _ := by
      unfold coefficientShearRetainedScaleOneConic
      have H := congrArg (· ≫ B) Horiginal.symm
      simpa only [Category.assoc] using congrArg (L ≫ ·) H


include h3 h4 hrt in
/-- The actual original second conic parameter retains the entire model specialization. -/
theorem coefficientShearOriginalConicSecond_specialization :
    Spec.map (CommRingCat.ofHom (conicPuncturedSecond UT cT hdz).toRingHom) ≫ CT ≫ M =
      L ≫ Spec.map (CommRingCat.ofHom (conicPuncturedSecond V c hcz).toRingHom) ≫ F ≫ B := by
  have Hmodel := coefficientShearSpecialization_retainedScaleOneConic hπ data K T f 0 t
    j hj m hm hs hp h3 h4 hr gs gp g3 g4 gt hrt
  have Hparam := conicPuncturedSecond_spec_coefficient f.toRingHom U UT c cT ha hc hcz hdz
  have Horiginal := zeroResidueConicSecond_spec_eq_shear D hk0 hk d hs hp h3 h4 hr hcz
  calc
    _ = Spec.map (CommRingCat.ofHom (conicPuncturedSecond UT cT hdz).toRingHom) ≫ p ≫ CS :=
      congrArg (_ ≫ ·) Hmodel
    _ = L ≫ Spec.map (CommRingCat.ofHom (conicPuncturedSecond U c hcz).toRingHom) ≫ CS := by
      simpa only [Category.assoc] using congrArg (· ≫ CS) Hparam
    _ = _ := by
      unfold coefficientShearRetainedScaleOneConic
      have H := congrArg (· ≫ B) Horiginal.symm
      simpa only [Category.assoc] using congrArg (L ≫ ·) H


end FLT.Mazur.WeierstrassDividedDepth
