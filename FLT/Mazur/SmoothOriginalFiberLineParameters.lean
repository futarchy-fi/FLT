/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedTranslationOriginalFiber
public import FLT.Mazur.SmoothOrderedLineParameters

/-!
# The original smooth family parametrizes all geometric fiber lines

With an ample fixed line on the given algebraically closed integral fiber,
every original fiber line is recovered from a translation on an ordered
power of the original relative curve. The parameter schemes remain smooth
over the original base. No extension of the arbitrary input line is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {k : Type} [Field k] [IsAlgClosed k] {C X S : Scheme} [IsIntegral C]
  {c : C ⟶ X} {q : C ⟶ Spec (.of k)} {f : X ⟶ S} {g : Spec (.of k) ⟶ S}
  (H : IsPullback c q f g) [IsProper f] [SmoothOfRelativeDimension 1 f]
  {B : X.Modules} (hB : LocallyFreeRankOne B)
  (hAmp : AmpleLineBundle ((Scheme.Modules.pullback c).obj B))
  {L : C.Modules} (hL : LocallyFreeRankOne L)

include hB hAmp hL in
/-- Every original geometric-fiber line comes from a translation on the original smooth base. -/
theorem exists_smooth_originalFiber_line_parameter :
    ∃ (n d : ℕ) (p : Fin d → (Spec (.of k) ⟶ C)) (hp : ∀ i, p i ≫ q = 𝟙 _),
      0 < n ∧ Smooth (base f d) ∧
      Nonempty ((Scheme.Modules.pullback (fiberCurveMap H d p hp)).obj
        (translationLine f d (tensorPower B n)) ≅ L) := by
  let _ : IsProper q := MorphismProperty.of_isPullback H inferInstance
  let _ : SmoothOfRelativeDimension 1 q := MorphismProperty.of_isPullback H inferInstance
  obtain ⟨n, I, hI, hn, _, _, _, ⟨e⟩⟩ := exists_ample_twist_line_divisor q
    (smoothCurveDimension q inferInstance inferInstance) hAmp hL
  obtain ⟨d, p, hp, he⟩ := exists_orderedCartier_point_factorization q hI
  let _ := SmoothOfRelativeDimension.smooth 1 f
  exact ⟨n, d, p, hp, hn, base_smooth f d,
    ⟨translationPowerFiberIso H d p hp B hB n I hI he ≪≫ e⟩⟩

include hB hAmp hL in
/-- The original curve's fixed smooth parameter family recovers the original fiber Picard class. -/
theorem exists_smooth_originalFiber_picard_parameter :
    ∃ (n d : ℕ) (p : Fin d → (Spec (.of k) ⟶ C)) (hp : ∀ i, p i ≫ q = 𝟙 _),
      0 < n ∧ Smooth (base f d) ∧
      SchemePicard.pullback (fiberCurveMap H d p hp)
        (SchemePicard.mk (translationLine f d (tensorPower B n))
          (translationLine_rankOne f d (hB.tensorPower n))) = SchemePicard.mk L hL := by
  obtain ⟨n, d, p, hp, hn, hs, ⟨e⟩⟩ :=
    exists_smooth_originalFiber_line_parameter H hB hAmp hL
  refine ⟨n, d, p, hp, hn, hs, ?_⟩
  rw [SchemePicard.pullback_mk]
  exact SchemePicard.mk_eq_of_iso _ _ e

end FLT.Mazur.FCurve
