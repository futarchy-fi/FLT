/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkedCubicComparison

/-!
# Inverse comparison of independently marked cubics

The inverse constructed comparison retains the coefficient base, marking and
actual whole-family isomorphism. These equations allow direct affine charts
to map to iterated restrictions without choosing compatible frames.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {E F : GeneralizedEllipticCurve S} (e : E ≅ F)
  (s : 𝟙_ (Over S) ⟶ E.group) (t : 𝟙_ (Over S) ⟶ F.group)
  (hs : s ≫ e.hom.group = t) (a : SmoothMarkingFrame E s) (b : SmoothMarkingFrame F t)
local notation "W" => smoothMarkingWeierstrassCurve E s a
local notation "V" => smoothMarkingWeierstrassCurve F t b
local notation "i" => markedCubicComparison e s t hs a b

/-- The inverse cubic comparison preserves the coefficient base. -/
@[reassoc] theorem markedCubicComparison_inv_over :
    (i).inv ≫ integralCurveStructure V = integralCurveStructure W := by
  rw [← markedCubicComparison_over e s t hs a b, Iso.inv_hom_id_assoc]

/-- The inverse cubic comparison preserves the marked point. -/
@[reassoc] theorem markedCubicComparison_inv_zero :
    integralCurveZero W ≫ (i).inv = integralCurveZero V := by
  rw [← markedCubicComparison_zero e s t hs a b, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The inverse cubic comparison retains the original forward family isomorphism. -/
@[reassoc] theorem markedCubicComparison_inv_whole :
    smoothMarkingToIntegralCubic E s a ≫ (i).inv =
      e.hom.curve.left ≫ smoothMarkingToIntegralCubic F t b := by
  apply (cancel_mono (i).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    markedCubicComparison_whole, ← Category.assoc]
  have he := ((forgetCurve ⋙ Over.forget S).mapIso e).hom_inv_id
  change e.hom.curve.left ≫ e.inv.curve.left = 𝟙 _ at he
  rw [he, Category.id_comp]

end FLT.Mazur.GeneralizedEllipticCurve
