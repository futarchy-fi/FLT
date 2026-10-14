/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginDirectImage
public import FLT.Mazur.FunctionSheafGradedSections

/-!
# The full original complete-base section-ring comparison

Every tensor degree is compared by the original contraction and the original
origin-ideal line isomorphism. The resulting bijection preserves multiplication.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart SectionGradedMultiplication SectionGradedSum
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "A" => originDivisorLine (W) 1
local notation "L" => completePointLine K n h i
local notation "e" => completePointOriginLineIso K n h i

/-- All local tensor-degree sections descend along the unchanged contraction and line map. -/
theorem completePointSectionPullback_bijective (m : ℕ) (V : (integralCurve (W)).Opens) :
    Function.Bijective (SectionGradedLinePullback.sectionMap (g) (e) m V) := by
  let _ := completePointToIntegralCubic_unitMap_isIso K n h i
  exact FunctionSheafGradedSections.sectionMap_bijective (g)
    (completePointOriginLine_rankOne K n h i 1) (e) m V

/-- The entire original marking section ring is the cubic-origin section ring. -/
def completePointSectionRingIso :
    SectionGradedSum.Sections (A) ⊤ ≃+* SectionGradedSum.Sections (L) ⊤ := by
  let _ := completePointToIntegralCubic_unitMap_isIso K n h i
  exact FunctionSheafGradedSections.ringEquiv (g)
    (completePointOriginLine_rankOne K n h i 1) (e)

/-- The equivalence uses the original adjunction-unit pullback in each degree. -/
theorem completePointSectionRingIso_of (m : ℕ) (s : Piece (A) ⊤ m) :
    completePointSectionRingIso K n h i (of (A) ⊤ m s) =
      of (L) ⊤ m (SectionGradedLinePullback.sectionMap (g) (e) m ⊤ s) :=
  SectionGradedLinePullback.ringHom_of (g) (e) m s

/-- The ring equivalence retains the original map of base functions in degree zero. -/
theorem completePointSectionRingIso_zero (r : Γ(integralCurve (W), ⊤)) :
    completePointSectionRingIso K n h i (of (A) ⊤ 0 r) =
      of (L) ⊤ 0 ((g).appTop r) := by
  rw [completePointSectionRingIso_of, SectionGradedLinePullback.sectionMap_zero]
  rfl

/-- Every original homogeneous component is identified onto the same degree. -/
theorem completePointSectionRingIso_grade (m : ℕ) :
    (completePointSectionRingIso K n h i) '' (grade (A) ⊤ m : Set _) =
      (grade (L) ⊤ m : Set _) := by
  let _ := completePointToIntegralCubic_unitMap_isIso K n h i
  exact FunctionSheafGradedSections.ringEquiv_grade (g)
    (completePointOriginLine_rankOne K n h i 1) (e) m

/-- The equivalence preserves and reflects the actual internal tensor grading. -/
theorem completePointSectionRingIso_mem_grade_iff (m : ℕ)
    (a : SectionGradedSum.Sections (A) ⊤) :
    completePointSectionRingIso K n h i a ∈ grade (L) ⊤ m ↔ a ∈ grade (A) ⊤ m := by
  change completePointSectionRingIso K n h i a ∈ (grade (L) ⊤ m : Set _) ↔
    a ∈ (grade (A) ⊤ m : Set _)
  rw [← completePointSectionRingIso_grade K n h i m]
  exact (completePointSectionRingIso K n h i).injective.mem_set_image

end FLT.Mazur.PolygonInfinitesimalStages
