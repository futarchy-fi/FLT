/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSelectorQuotient

/-!
# Full scheme kernels of constructed representative quotients

Division of the actual representative arrows constructs an original relation
arrow on every quotient-kernel test. This proves the full scheme pullback,
with no reducedness hypothesis and no preassigned quotient-kernel certificate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSelectorQuotient
open RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (r : A.left ⟶ D.left) (hr : r ≫ p.left = 𝟙 A.left)
  (hi : p.left ≫ r ≫ q.left = q.left ≫ r ≫ q.left)
local notation "v" => projection r hr hi
variable {Y : Scheme.{u}} (x y : Y ⟶ A.left)

/-- Equality on the constructed quotient identifies the two selected representatives. -/
theorem representative_eq (hxy : x ≫ v = y ≫ v) : (x ≫ r) ≫ q.left = (y ≫ r) ≫ q.left := by
  simpa only [Category.assoc, projection_inclusion] using
    congrArg (fun a ↦ a ≫ inclusion (q := q) r) hxy

/-- Divide the actual arrows to recover an arrow in the FULL original relation. -/
def kernelLift (hxy : x ≫ v = y ≫ v) : Y ⟶ D.left :=
  divideOriginal e (x ≫ r) (y ≫ r) (representative_eq r hr hi x y hxy)

@[reassoc]
theorem kernelLift_fst (hxy : x ≫ v = y ≫ v) : kernelLift e r hr hi x y hxy ≫ p.left = x := by
  rw [kernelLift, divideOriginal_fst, Category.assoc, hr, Category.comp_id]

@[reassoc]
theorem kernelLift_snd (hxy : x ≫ v = y ≫ v) : kernelLift e r hr hi x y hxy ≫ q.left = y := by
  rw [kernelLift, divideOriginal_snd, Category.assoc, hr, Category.comp_id]

/-- The construction is natural on arbitrary scheme tests, including nonreduced ones. -/
theorem kernelLift_comp (hxy : x ≫ v = y ≫ v) {Z : Scheme.{u}} (a : Z ⟶ Y) :
    a ≫ kernelLift e r hr hi x y hxy = kernelLift e r hr hi (a ≫ x) (a ≫ y)
      (by simpa only [Category.assoc] using congrArg (fun b ↦ a ≫ b) hxy) := by
  apply originalArrow_ext e
  · rw [Category.assoc, kernelLift_fst, kernelLift_fst]
  · rw [Category.assoc, kernelLift_snd, kernelLift_snd]

include e in
/-- No part of the original relation or its scheme structure is lost by the quotient. -/
theorem isPullback : IsPullback p.left q.left v v := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (condition r hr hi)
    (fun c ↦ kernelLift e r hr hi c.fst c.snd c.condition)
    (fun c ↦ kernelLift_fst e r hr hi c.fst c.snd c.condition)
    (fun c ↦ kernelLift_snd e r hr hi c.fst c.snd c.condition) ?_)
  intro c a ha hb
  apply originalArrow_ext e
  · exact ha.trans (kernelLift_fst e r hr hi c.fst c.snd c.condition).symm
  · exact hb.trans (kernelLift_snd e r hr hi c.fst c.snd c.condition).symm

/-- Recovering an existing original arrow returns that arrow exactly. -/
theorem kernelLift_original (a : Y ⟶ D.left) :
    kernelLift e r hr hi (a ≫ p.left) (a ≫ q.left)
      (by simpa only [Category.assoc] using
        congrArg (fun b ↦ a ≫ b) (condition r hr hi)) = a := by
  apply originalArrow_ext e
  · exact kernelLift_fst e r hr hi _ _ _
  · exact kernelLift_snd e r hr hi _ _ _

end FLT.Mazur.SchemeRelationSelectorQuotient
