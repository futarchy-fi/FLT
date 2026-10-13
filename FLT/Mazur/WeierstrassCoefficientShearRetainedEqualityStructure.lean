/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedEqualityDescent
public import FLT.Mazur.WeierstrassCoefficientShearRetainedDescentStructure
public import FLT.Mazur.WeierstrassCoefficientShearEqualityParameterStructure
public import FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent
public import FLT.Mazur.ProjectiveLineScaling
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEqualityDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedDescentStructure

/-!
# Coefficient structure of the full final retained descent

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

variable (p : Y ⟶ Spec (.of S))
  (hf : f ≫ p = ProjectiveLine.toBase S)
  (hg₁ : g₁ ≫ p = ProjectiveLine.toBase S) (hg₂ : g₂ ≫ p = ProjectiveLine.toBase S)

include hf hg₁ hg₂ in
/-- The original full final retained descent preserves its coefficient field. -/
theorem coefficientShearRetainedEqualityDesc_structure :
    coefficientShearRetainedEqualityDesc
      data S r j hj hs hp h3 h4 hc hr a ha f g₁ g₂ w₁ w₂ ≫ p =
        coefficientShearAtlasStructure data S r (j + 1) hj (.inr ⟨j, Nat.lt_succ_self j⟩) := by
  rw [coefficientShearRetainedEqualityDesc]
  apply coefficientShearRetainedEquationDesc_structure
  · rw [Category.assoc, hf, coefficientShearEqualityConicParameter_structure]
  · rw [Category.assoc, Category.assoc, hg₁, ProjectiveLine.right_toBase,
      ProjectiveLine.chartScaling_toBase]
  · rw [Category.assoc, Category.assoc, hg₂, ProjectiveLine.right_toBase,
      ProjectiveLine.chartScaling_toBase]

end FLT.Mazur.WeierstrassDividedDepth
