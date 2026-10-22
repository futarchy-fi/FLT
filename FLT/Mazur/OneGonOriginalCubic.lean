/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonOriginalAction
public import FLT.Mazur.PolygonGeneralizedPinchingIso
public import FLT.Mazur.ArithmeticOneGonOriginalFiber

/-!
# Full Weierstrass presentation of an original abstract one-gon

No equation or compatible group coordinate is specified on the input curve.
Its pinching realization, actual identity, group and action construct an
isomorphism to the arithmetic boundary Weierstrass cubic over the original field.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OneGonOriginalCubic
open PolygonPinching OneGonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K]
  (E : GeneralizedEllipticCurve (Spec (.of K)))
  (p : components K 1 ⟶ E.curve) (q : nodes K 1 ⟶ E.curve)
  (h : IsPushout (toComponents K 1 Nat.zero_lt_one) (toNodes K 1) p q)

/-- The whole original abstract one-gon is the arithmetic boundary generalized curve. -/
def boundaryIso : E ≅ ArithmeticOneGonTorus.boundaryCurve K :=
  (OneGonOriginalAction.originalIso E p q h).symm ≪≫
    (PolygonGeneralizedPinchingIso.generalizedIso 1 Nat.zero_lt_one
      (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
      (OneGonGlobalPushout.isPushout K Nat.zero_lt_one) p q h).symm ≪≫
    ArithmeticOneGonOriginalFiber.curveIso K

/-- A one-gon property suffices for a full original generalized-curve Weierstrass presentation. -/
theorem exists_boundaryIso (hc : IsNeronNGon E.curve 1 Nat.zero_lt_one) :
    Nonempty (E ≅ ArithmeticOneGonTorus.boundaryCurve K) := by
  obtain ⟨p, q, h⟩ := hc
  exact ⟨boundaryIso E p q h⟩

/-- The complete cubic presentation preserves the actual original identity. -/
@[reassoc] theorem boundaryIso_identity :
    E.identitySection ≫ (boundaryIso E p q h).hom.curve =
      (ArithmeticOneGonTorus.boundaryCurve K).identitySection :=
  (boundaryIso E p q h).hom.identitySection

/-- The complete presentation intertwines the original whole action, including the node. -/
theorem boundaryIso_action :
    E.act ≫ (boundaryIso E p q h).hom.curve =
      ((boundaryIso E p q h).hom.group ⊗ₘ (boundaryIso E p q h).hom.curve) ≫
        (ArithmeticOneGonTorus.boundaryCurve K).act :=
  (boundaryIso E p q h).hom.action

end FLT.Mazur.OneGonOriginalCubic
