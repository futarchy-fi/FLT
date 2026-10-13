/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNormalizationInfinity

/-!
# Infinity parameters for an equation identified with the split nodal cubic

Transport the proved infinity section to the actual equation. The source remains
its original complete chart, with the original structure and cubic inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (a : Kˣ)
  (he : W = splitNodalEquation a)

/-- The full infinity chart of the actual equation has its original projective parameter. -/
def splitEquationInfinityParameter : chartScheme W 1 ⟶ scheme K := by
  subst W
  exact (splitNodalTorusIso a).inv ≫ infinityTorusChart a

/-- The parameter map preserves the actual field structure on the whole chart. -/
@[reassoc] theorem splitEquationInfinityParameter_structure :
    splitEquationInfinityParameter W a he ≫ toBase K = chartStructure W 1 := by
  subst W
  change ((splitNodalTorusIso a).inv ≫ infinityTorusChart a) ≫ _ = _
  rw [Category.assoc, infinityTorusChart_toBase]
  change (splitNodalTorusIso a).inv ≫ (MultiplicativeGroupScheme.gm K).hom = _
  rw [← splitNodalTorusIso_structure a, Iso.inv_hom_id_assoc]

variable (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)

/-- The entire original infinity inclusion factors through the existing complete normalization. -/
@[reassoc] theorem splitEquationInfinityParameter_normalization :
    splitEquationInfinityParameter W a he ≫ splitCompleteNormalization W h₂ h₃ h₄ h₆ =
      integralCurveChart W 1 := by
  subst W
  change ((splitNodalTorusIso a).inv ≫ infinityTorusChart a) ≫ _ = _
  rw [Category.assoc, splitCompleteNormalization_infinity_section]

end FLT.Mazur
