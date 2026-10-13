/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedZeroDescent
public import FLT.Mazur.WeierstrassCoefficientShearRetainedDescentStructure
public import FLT.Mazur.WeierstrassProjectiveFiberDescentStructure
public import FLT.Mazur.WeierstrassConicZeroProjectiveDescent
public import FLT.Mazur.ProjectiveLineScaling
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedZeroDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedDescentStructure

/-!
# Coefficient structure of the original retained zero descent

Retain both complete conic parameters and the independently scaled horizontal lines.
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
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (i : Fin t)
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => q (Data.b6 d)
variable (hs : algebraMap R S (π ^ (start + i.val)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "e" => coefficientShearMiddleEquiv W (π ^ (start + i.val)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4
local notation "h2" => coefficientShear_a₂_zero W S r hr

local notation "E" => coefficientShearRetainedEquationIso data S r t ht i hs hp h3 h4
variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)
  (hc : algebraMap R S (data ⟨i.val + 1, by omega⟩).b6 = 0)
  (k₁ k₂ : Sˣ) {Y : Scheme.{u}} (f₁ f₂ g₁ g₂ : ProjectiveLine.scheme S ⟶ Y)
  (w₁ : ProjectiveLine.zero S ≫ f₁ = ProjectiveLine.infinity S ≫ g₁)
  (w₂ : ProjectiveLine.zero S ≫ f₂ = ProjectiveLine.infinity S ≫ g₂)
local notation "Z" => conicZeroAffineIso c hc
local notation "p₁" => (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c
local notation "p₂" => (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c
local notation "C" => conicZeroProjectiveDesc a c ha hc f₁ f₂
local notation "L₁" => ProjectiveLine.chartScaling S k₁ ≫ ProjectiveLine.right S ≫ g₁
local notation "L₂" => ProjectiveLine.chartScaling S k₂ ≫ ProjectiveLine.right S ≫ g₂

variable (p : Y ⟶ Spec (.of S))
  (hf₁ : f₁ ≫ p = ProjectiveLine.toBase S) (hf₂ : f₂ ≫ p = ProjectiveLine.toBase S)
  (hg₁ : g₁ ≫ p = ProjectiveLine.toBase S) (hg₂ : g₂ ≫ p = ProjectiveLine.toBase S)

include hf₁ hf₂ hg₁ hg₂ in
/-- All four original component maps descend over the coefficient field. -/
theorem coefficientShearRetainedZeroDesc_structure :
    coefficientShearRetainedZeroDesc
      data S r t ht i hs hp h3 h4 hr ha hc k₁ k₂ f₁ f₂ g₁ g₂ w₁ w₂ ≫ p =
        coefficientShearAtlasStructure data S r t ht (.inr i) := by
  rw [coefficientShearRetainedZeroDesc]
  apply coefficientShearRetainedEquationDesc_structure
  · exact conicZeroProjectiveDesc_structure a c ha hc f₁ f₂ p hf₁ hf₂
  · rw [Category.assoc, Category.assoc, hg₁, ProjectiveLine.right_toBase,
      ProjectiveLine.chartScaling_toBase]
  · rw [Category.assoc, Category.assoc, hg₂, ProjectiveLine.right_toBase,
      ProjectiveLine.chartScaling_toBase]

end FLT.Mazur.WeierstrassDividedDepth
