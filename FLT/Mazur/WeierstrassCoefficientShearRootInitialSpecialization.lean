/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootInitialComponents
public import FLT.Mazur.WeierstrassCoefficientShearRetainedLineSpecialization
public import FLT.Mazur.ProjectiveLineCoefficientMap
public import FLT.Mazur.ProjectiveLineRightChartExt
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
import all FLT.Mazur.WeierstrassCoefficientShearRootInitialComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedLineSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
/-!
# Coefficient specialization of the complete initial projective components

Both independently glued initial components specialize with their original
projective parameters, signed reciprocal scales and affine origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type u) [Field S] [Field T] [Algebra R S] [Algebra R T]
  (f : S →ₐ[R] T) (r : S) (t : T)
  (h1 : 1 ≤ n) (m : ℕ) (hm : 1 + m ≤ n)
  (hs : algebraMap R S (π ^ start) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (gs : algebraMap R T (π ^ start) = 0) (gp : algebraMap R T π = 0)
  (g3 : algebraMap R T (data ⟨1, Nat.lt_succ_of_le h1⟩).b3 = 0)
  (g4 : algebraMap R T (data ⟨1, Nat.lt_succ_of_le h1⟩).b4 = 0)
  (gt : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
  (s3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (s4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (s6 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6 = 0)
  (t3 : algebraMap R T (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (t4 : algebraMap R T (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (t6 : algebraMap R T (data ⟨0, Nat.zero_lt_succ n⟩).b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (b : Tˣ) (hb : (b : T) = (rootShearCurve (W.map (algebraMap R T)) t).a₁)
  (hrt : f r = t)
local notation "CS₁" => coefficientShearRootInitialFirstComponent
  hπ data S r h1 m hm hs hp h3 h4 hr s3 s4 s6 a ha
local notation "CS₂" => coefficientShearRootInitialSecondComponent
  hπ data S r h1 m hm hs hp h3 h4 hr s3 s4 s6 a ha
local notation "CT₁" => coefficientShearRootInitialFirstComponent
  hπ data T t h1 m hm gs gp g3 g4 gt t3 t4 t6 b hb
local notation "CT₂" => coefficientShearRootInitialSecondComponent
  hπ data T t h1 m hm gs gp g3 g4 gt t3 t4 t6 b hb
local notation "M" => coefficientShearSpecialization hπ data S T r t (1 + m) hm f
local notation "P" => ProjectiveLine.coefficientMap f.toRingHom
local notation "base" => coefficientShearGluedStructure hπ data S r (1 + m) hm
include hrt

/-- The entire first projective component specializes with its original projective parameter. -/
@[reassoc] theorem coefficientShearRootInitialFirstComponent_specialization :
    CT₁ ≫ M = P ≫ CS₁ := by
  have hab : Units.map f.toRingHom a = b := by
    apply Units.ext
    change f (a : S) = (b : T)
    rw [ha, hb]
    exact rootShearTangent_coefficient W S r T f t hrt
  let _ : IsSeparated base := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.rightChart_hom_ext T base
  · rw [Category.assoc, coefficientShearSpecialization_structure,
      coefficientShearRootInitialFirstComponent_structure_assoc, Category.assoc,
      coefficientShearRootInitialFirstComponent_structure, ProjectiveLine.coefficientMap_toBase]
  · rw [coefficientShearRootInitialFirstComponent_right_assoc,
      ProjectiveLine.right_coefficientMap_assoc, coefficientShearRootInitialFirstComponent_right,
      coefficientShearSpecialization_retainedFirst hπ data S T f r t 0 h1 m hm
        hs hp h3 h4 hr gs gp g3 g4 gt hrt,
      ProjectiveLine.chartScaling_coefficient_assoc f.toRingHom a⁻¹ b⁻¹
        (by rw [map_inv, hab])]

/-- The entire opposite component specializes with the negative reciprocal scale unchanged. -/
@[reassoc] theorem coefficientShearRootInitialSecondComponent_specialization :
    CT₂ ≫ M = P ≫ CS₂ := by
  have hab : Units.map f.toRingHom a = b := by
    apply Units.ext
    change f (a : S) = (b : T)
    rw [ha, hb]
    exact rootShearTangent_coefficient W S r T f t hrt
  let _ : IsSeparated base := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.rightChart_hom_ext T base
  · rw [Category.assoc, coefficientShearSpecialization_structure,
      coefficientShearRootInitialSecondComponent_structure_assoc, Category.assoc,
      coefficientShearRootInitialSecondComponent_structure, ProjectiveLine.coefficientMap_toBase]
  · rw [coefficientShearRootInitialSecondComponent_right_assoc,
      ProjectiveLine.right_coefficientMap_assoc, coefficientShearRootInitialSecondComponent_right,
      coefficientShearSpecialization_retainedSecond hπ data S T f r t 0 h1 m hm
        hs hp h3 h4 hr gs gp g3 g4 gt hrt,
      ProjectiveLine.chartScaling_coefficient_assoc f.toRingHom (-a)⁻¹ (-b)⁻¹
        (by rw [map_inv, Units.map_neg, hab])]

end FLT.Mazur.WeierstrassDividedDepth
