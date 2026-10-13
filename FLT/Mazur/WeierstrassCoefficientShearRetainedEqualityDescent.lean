/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearEqualityChartParameters
public import FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent
public import FLT.Mazur.ProjectiveLineScaling
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent

/-!
# Descent on the final retained equation at equality depth

Use the actual completed conic with its original invertible divided constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)



local notation "q" => coefficientShearEqualityConicParameter
  data S r j hj hs hp h3 h4 hc hr a ha
local notation "E" => coefficientShearRetainedEquationIso
  data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ hs hp h3 h4
local notation "h2" => coefficientShear_a₂_zero W S r hr
variable {Y : Scheme.{u}} (f g₁ g₂ : ProjectiveLine.scheme S ⟶ Y)
  (w₁ : ProjectiveLine.zero S ≫ f = ProjectiveLine.infinity S ≫ g₁)
  (w₂ : ProjectiveLine.infinity S ≫ f = ProjectiveLine.infinity S ≫ g₂)
local notation "L₁" => ProjectiveLine.chartScaling S a ≫ ProjectiveLine.right S ≫ g₁
local notation "L₂" => ProjectiveLine.chartScaling S (-a) ≫ ProjectiveLine.right S ≫ g₂

/-- Descend the complete equality component and the two preceding branch charts. -/
@[irreducible] def coefficientShearRetainedEqualityDesc :
    coefficientShearAtlasObject data S r (j + 1) hj (.inr ⟨j, Nat.lt_succ_self j⟩) ⟶ Y :=
  coefficientShearRetainedEquationDesc data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩
    hs hp h3 h4 hr hu (q ≫ f) L₁ L₂
    (by rw [coefficientShearEqualityConicParameter_first_assoc,
            ProjectiveLine.chartZero_chartScaling_assoc]; exact w₁)
    (by rw [coefficientShearEqualityConicParameter_second_assoc,
            ProjectiveLine.chartZero_chartScaling_assoc]; exact w₂)
local notation "D" => coefficientShearRetainedEqualityDesc
  data S r j hj hs hp h3 h4 hc hr a ha f g₁ g₂ w₁ w₂

/-- The full retained conic maps through its actual completed equality component. -/
theorem coefficientShearRetainedEqualityDesc_conic :
    middleConicImmersion U c h2 ≫ (E).hom ≫ D = q ≫ f := by
  rw [coefficientShearRetainedEqualityDesc]
  erw [coefficientShearRetainedEquationDesc_conic
    data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ hs hp h3 h4 hr hu]

/-- The first full line retains its original tangent scale and projective component. -/
theorem coefficientShearRetainedEqualityDesc_first :
    middleLineImmersion U c h2 0 (middle_first_root U) ≫ (E).hom ≫ D = L₁ := by
  rw [coefficientShearRetainedEqualityDesc]
  erw [coefficientShearRetainedEquationDesc_first
    data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ hs hp h3 h4 hr hu]

/-- The opposite full line retains the original negative tangent scale. -/
theorem coefficientShearRetainedEqualityDesc_second :
    middleLineImmersion U c h2 (-(U).a₁) (middle_second_root U) ≫ (E).hom ≫ D = L₂ := by
  rw [coefficientShearRetainedEqualityDesc]
  erw [coefficientShearRetainedEquationDesc_second
    data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ hs hp h3 h4 hr hu]

/-- Full conic and line restrictions uniquely characterize the final retained descent. -/
theorem coefficientShearRetainedEqualityDesc_unique
    (m : coefficientShearAtlasObject data S r (j + 1) hj
      (.inr ⟨j, Nat.lt_succ_self j⟩) ⟶ Y)
    (hf : middleConicImmersion U c h2 ≫ (E).hom ≫ m = q ≫ f)
    (hg₁ : middleLineImmersion U c h2 0 (middle_first_root U) ≫ (E).hom ≫ m = L₁)
    (hg₂ : middleLineImmersion U c h2 (-(U).a₁) (middle_second_root U) ≫ (E).hom ≫ m = L₂) :
    m = D := by
  rw [coefficientShearRetainedEqualityDesc]
  exact coefficientShearRetainedEquationDesc_unique
    data S r (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ hs hp h3 h4 hr hu
    _ _ _ _ _ m hf hg₁ hg₂

end FLT.Mazur.WeierstrassDividedDepth
