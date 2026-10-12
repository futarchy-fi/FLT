/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootChange
public import FLT.Mazur.WeierstrassSuccessiveShearLineRootChange
public import FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Actual retained line embeddings survive a change of chosen tangent root

Comparison uses the complete original tensor maps and the whole model
isomorphism. The affine line and its node origin are both retained.
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
  (S : Type u) [CommRing S] [Algebra R S] (r s : S)
  (j k : ℕ) (hj : j ≤ n) (hk : k + 1 ≤ j)
  (hscale : algebraMap R S (π ^ (start + k)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨k + 1, by omega⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨k + 1, by omega⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (hs : s ^ 2 + algebraMap R S W.a₁ * s - algebraMap R S W.a₂ = 0)
  (v w : S)
  (hv : v * (v + (rootShearCurve (W.map (algebraMap R S)) r).a₁) = 0)
  (hw : w * (w + (rootShearCurve (W.map (algebraMap R S)) s).a₁) = 0)
local notation "C" => coefficientShearRootChange hπ data S r s j hj
local notation "Lr" => coefficientShearRetainedLine hπ data S r j hj ⟨k, by omega⟩
  hscale hp h3 h4 hr v hv
local notation "Ls" => coefficientShearRetainedLine hπ data S s j hj ⟨k, by omega⟩
  hscale hp h3 h4 hs w hw

/-- Equality of original slopes identifies the full retained affine line in both models. -/
@[reassoc] theorem coefficientShearRootChange_retainedLine (hvw : v + r = w + s) :
    Lr ≫ (C).hom = Ls := by
  rw [← coefficientShearRetainedTensorChart_line,
    ← coefficientShearRetainedTensorChart_line, Category.assoc,
    coefficientShearRootChange_retainedTensorChart hπ data S r s j hj k hk]
  rw [tensorShearLineMap_rootChange W (π ^ (start + k)) π
    (data ⟨k + 1, by omega⟩).b3 (data ⟨k + 1, by omega⟩).b4
    (data ⟨k + 1, by omega⟩).b6 S r s hscale hp h3 h4 hr hs v w hv hw hvw]

local notation "Ur" => rootShearCurve (W.map (algebraMap R S)) r
local notation "Us" => rootShearCurve (W.map (algebraMap R S)) s
local notation "lineR" => coefficientShearRetainedLine hπ data S r j hj ⟨k, by omega⟩
  hscale hp h3 h4 hr
local notation "lineS" => coefficientShearRetainedLine hπ data S s j hj ⟨k, by omega⟩
  hscale hp h3 h4 hs

/-- The complete first line becomes the opposite line when the ordered tangent root changes. -/
@[reassoc] theorem coefficientShearRootChange_retainedFirst
    (hrs : r + s = -algebraMap R S W.a₁) :
    lineR 0 (middle_first_root Ur) ≫ (C).hom =
      lineS (-(Us).a₁) (middle_second_root Us) := by
  apply coefficientShearRootChange_retainedLine hπ data S r s j k hj hk
  rw [zero_add, (rootShearCurve_coefficients (W := W.map (algebraMap R S)) s).1]
  change r = -(algebraMap R S W.a₁ + 2 * s) + s
  linear_combination hrs

/-- The entire opposite line becomes the first line, retaining its original affine parameter. -/
@[reassoc] theorem coefficientShearRootChange_retainedSecond
    (hrs : r + s = -algebraMap R S W.a₁) :
    lineR (-(Ur).a₁) (middle_second_root Ur) ≫ (C).hom =
      lineS 0 (middle_first_root Us) := by
  apply coefficientShearRootChange_retainedLine hπ data S r s j k hj hk
  rw [zero_add, (rootShearCurve_coefficients (W := W.map (algebraMap R S)) r).1]
  change -(algebraMap R S W.a₁ + 2 * r) + r = s
  linear_combination -hrs

end FLT.Mazur.WeierstrassDividedDepth
