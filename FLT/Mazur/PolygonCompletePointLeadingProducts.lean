/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLeadingNonzeroProduct
public import FLT.Mazur.PolygonCompletePointFunctionDimensions

/-!
# Nonzero leading products on every original field square

The retained marking identifies its actual closed divisor with the base
field. The original new sections have nonzero restrictions there, and their
actual graded products remain nonzero on that same marked-point fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- Original new sections multiply nontrivially in the actual retained marked-point fiber. -/
theorem completeCartesianPointNewSection_product_restrict_ne_zero
    (i : Fin n) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    pullGlobal (completeCartesianMarking K n h s p q hs i).ker.subschemeι _
      (SectionGradedMultiplication.mul (completeCartesianPointLine K n h s p q hs i)
        ⊤ (a + 1) (b + 1)
        (completeCartesianPointNewSection K n h L s p q hs i a ha)
        (completeCartesianPointNewSection K n h L s p q hs i b hb)) ≠ 0 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  have ht := markedPointLeading_product_restriction_ne_zero q
    (completeCartesianMarking K n h s p q hs i)
    (completeCartesianMarking_snd K n h s p q hs i)
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1 a b
    ((moduleScalarH0Equiv q _).symm
      (completeCartesianPointNewSection K n h L s p q hs i a ha))
    ((moduleScalarH0Equiv q _).symm
      (completeCartesianPointNewSection K n h L s p q hs i b hb))
    (completeCartesianPointNewSection_leading_ne_zero K n h L s p q hs i a ha)
    (completeCartesianPointNewSection_leading_ne_zero K n h L s p q hs i b hb)
  simpa only [completeCartesianPointLine, LinearEquiv.apply_symm_apply] using ht

end FLT.Mazur.PolygonInfinitesimalStages
