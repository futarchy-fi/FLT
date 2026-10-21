/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCoefficientIso

/-!
# Parameter equality for the full arithmetic one-gon

Equality of parameters induces an isomorphism of generalized curves, retaining
the actual whole-curve equality transport. These isomorphisms compose directly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open OneGonSmoothing GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {r s t : R}

/-- Transport the arithmetic generalized curve along an equality of its parameter. -/
irreducible_def parameterIso (h : s = t)
    (hs : IsUnit (1 + 432 * s)) (ht : IsUnit (1 + 432 * t)) :
    curve s hs ≅ curve t ht := by
  subst t
  exact Iso.refl _

/-- The generalized parameter comparison retains the sealed whole-cubic transport. -/
theorem parameterIso_curve (h : s = t)
    (hs : IsUnit (1 + 432 * s)) (ht : IsUnit (1 + 432 * t)) :
    (parameterIso h hs ht).hom.curve = (parameterCurveIso h).hom := by
  subst t
  rw [parameterIso_def, parameterCurveIso_def]
  rfl

/-- The underlying scheme map is precisely the original equality transport. -/
theorem parameterIso_curve_left (h : s = t)
    (hs : IsUnit (1 + 432 * s)) (ht : IsUnit (1 + 432 * t)) :
    (parameterIso h hs ht).hom.curve.left =
      eqToHom (congrArg (fun x : R => (OneGonSmoothing.family x).left) h) := by
  subst t
  rw [parameterIso_def]
  rfl

/-- Direct and successive parameter transports agree as full generalized-curve maps. -/
@[reassoc] theorem parameterIso_trans (h : r = s) (k : s = t)
    (hr : IsUnit (1 + 432 * r)) (hs : IsUnit (1 + 432 * s))
    (ht : IsUnit (1 + 432 * t)) :
    (parameterIso h hr hs).hom ≫ (parameterIso k hs ht).hom =
      (parameterIso (h.trans k) hr ht).hom := by
  subst s t
  rw [parameterIso_def]
  exact Category.id_comp _

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
