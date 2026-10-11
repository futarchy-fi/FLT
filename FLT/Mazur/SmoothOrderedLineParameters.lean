/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCartierPointFactorization
public import FLT.Mazur.OrderedDivisorTranslation
public import FLT.Mazur.OrderedCurvePowerSmooth
public import FLT.Mazur.SchemePicardPullback
public import FLT.Mazur.AmpleTwistLineDivisor

/-!
# Smooth ordered parameters recovering every curve line

Fixing an ample line gives one countable family of smooth ordered parameter
schemes and actual universal translation lines. Every line on a proper smooth
integral curve over an algebraically closed field is the specialization of a
member of this family. Recovery is an isomorphism on the unchanged original
curve. This is a field-level result, not yet coverage of arbitrary Picard tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]
  {B L : X.Modules} (hB : AmpleLineBundle B) (hL : LocallyFreeRankOne L)

include hB hL in
/-- One fixed smooth ordered family recovers every original line by actual specialization. -/
theorem exists_smooth_ordered_line_parameter :
    ∃ (n d : ℕ) (a : Spec (.of k) ⟶ space f d) (ha : a ≫ base f d = 𝟙 _),
      0 < n ∧ Smooth (base f d) ∧
      LocallyFreeRankOne (translationLine f d (tensorPower B n)) ∧
      Nonempty ((Scheme.Modules.pullback (sectionCurveMap f d a ha)).obj
        (translationLine f d (tensorPower B n)) ≅ L) := by
  obtain ⟨n, I, hI, hn, _, _, _, ⟨e⟩⟩ := exists_ample_twist_line_divisor f
    (smoothCurveDimension f inferInstance inferInstance) hB hL
  obtain ⟨d, a, ha, he⟩ := exists_orderedCartier_parameter f hI
  have he' : (divisorIdeal f d).comap (sectionCurveMap f d a ha) = I := by
    rw [divisorIdeal_section_comap, ← he]
  let _ := SmoothOfRelativeDimension.smooth 1 f
  exact ⟨n, d, a, ha, hn, base_smooth f d,
    translationLine_rankOne f d (hB.2.1.tensorPower n),
    ⟨translationLineSectionIso f d a ha (tensorPower B n) I hI he' ≪≫ e⟩⟩

include hB hL in
/-- The same fixed family recovers the original Picard class by its actual pullback map. -/
theorem exists_smooth_ordered_picard_parameter :
    ∃ (n d : ℕ) (a : Spec (.of k) ⟶ space f d) (ha : a ≫ base f d = 𝟙 _),
      0 < n ∧ Smooth (base f d) ∧
      SchemePicard.pullback (sectionCurveMap f d a ha)
        (SchemePicard.mk (translationLine f d (tensorPower B n))
          (translationLine_rankOne f d (hB.2.1.tensorPower n))) = SchemePicard.mk L hL := by
  obtain ⟨n, d, a, ha, hn, hs, ht, ⟨e⟩⟩ := exists_smooth_ordered_line_parameter f hB hL
  refine ⟨n, d, a, ha, hn, hs, ?_⟩
  rw [SchemePicard.pullback_mk]
  exact SchemePicard.mk_eq_of_iso _ _ e

end FLT.Mazur.FCurve
