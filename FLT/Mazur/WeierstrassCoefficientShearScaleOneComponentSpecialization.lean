/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedLineSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearRetainedLineSpecialization
public import FLT.Mazur.ProjectiveLineCoefficientMap
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneComponentStructure
public import FLT.Mazur.ProjectiveLineRightChartExt
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneComponents
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneComponentStructure
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedFullConic

/-!
# Actual coefficient specialization of complete scale-one projective components

Specialize the independently constructed projective components, including
both origins, using the original full retained line on the dense right chart.
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
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)
  (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 2, by omega⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 2, by omega⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (gs : algebraMap R T (π ^ (start + j)) = 1) (gp : algebraMap R T π = 0)
  (g3 : algebraMap R T (data ⟨j + 2, by omega⟩).b3 = 0)
  (g4 : algebraMap R T (data ⟨j + 2, by omega⟩).b4 = 0)
  (gt : t ^ 2 + algebraMap R T W.a₁ * t - algebraMap R T W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (b : Tˣ) (hb : (b : T) = (rootShearCurve (W.map (algebraMap R T)) t).a₁)
  (hrt : f r = t) (hab : Units.map f.toRingHom a = b)
local notation "CS₁" => coefficientShearScaleOneFirstComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "CS₂" => coefficientShearScaleOneSecondComponent
  hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha
local notation "CT₁" => coefficientShearScaleOneFirstComponent
  hπ data T t j hj hjNext m hm gs gp g3 g4 gt b hb
local notation "CT₂" => coefficientShearScaleOneSecondComponent
  hπ data T t j hj hjNext m hm gs gp g3 g4 gt b hb
local notation "M" => coefficientShearSpecialization hπ data S T r t (j + 2 + m) hm f
local notation "P" => ProjectiveLine.coefficientMap f.toRingHom
local notation "base" => coefficientShearGluedStructure hπ data S r (j + 2 + m) hm
local notation "hsNext" => coefficientShearAdjacent_scale S hp (k := start + j)
local notation "gsNext" => coefficientShearAdjacent_scale T gp (k := start + j)
include hrt hab

/-- The entire first projective component specializes with its original projective parameter. -/
@[reassoc] theorem coefficientShearScaleOneFirstComponent_specialization :
    CT₁ ≫ M = P ≫ CS₁ := by
  let _ : IsSeparated base := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.rightChart_hom_ext T base
  · rw [Category.assoc, coefficientShearSpecialization_structure,
      coefficientShearScaleOneFirstComponent_structure_assoc, Category.assoc,
      coefficientShearScaleOneFirstComponent_structure, ProjectiveLine.coefficientMap_toBase]
  · rw [coefficientShearScaleOneFirstComponent_right_assoc,
      ProjectiveLine.right_coefficientMap_assoc, coefficientShearScaleOneFirstComponent_right,
      coefficientShearSpecialization_retainedFirst hπ data S T f r t (j + 1) hjNext m hm
        hsNext hp h3 h4 hr gsNext gp g3 g4 gt hrt,
      ProjectiveLine.chartScaling_coefficient_assoc f.toRingHom a⁻¹ b⁻¹
        (by rw [map_inv, hab])]

/-- The entire opposite component specializes with the negative reciprocal scale unchanged. -/
@[reassoc] theorem coefficientShearScaleOneSecondComponent_specialization :
    CT₂ ≫ M = P ≫ CS₂ := by
  let _ : IsSeparated base := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.rightChart_hom_ext T base
  · rw [Category.assoc, coefficientShearSpecialization_structure,
      coefficientShearScaleOneSecondComponent_structure_assoc, Category.assoc,
      coefficientShearScaleOneSecondComponent_structure, ProjectiveLine.coefficientMap_toBase]
  · rw [coefficientShearScaleOneSecondComponent_right_assoc,
      ProjectiveLine.right_coefficientMap_assoc, coefficientShearScaleOneSecondComponent_right,
      coefficientShearSpecialization_retainedSecond hπ data S T f r t (j + 1) hjNext m hm
        hsNext hp h3 h4 hr gsNext gp g3 g4 gt hrt,
      ProjectiveLine.chartScaling_coefficient_assoc f.toRingHom (-a)⁻¹ (-b)⁻¹
        (by rw [map_inv, Units.map_neg, hab])]

end FLT.Mazur.WeierstrassDividedDepth
