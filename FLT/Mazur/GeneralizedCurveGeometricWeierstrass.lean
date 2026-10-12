/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGeometricGroupIso
public import FLT.Mazur.WeierstrassGeneralizedEllipticModel

/-!
# Actual geometric generalized curves have full Weierstrass presentations

The constructed group isomorphism extends through the original smooth
inclusions. It preserves the complete curve, its group and the original action.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (E : GeneralizedEllipticCurve (Spec (.of k)))
  [IsIntegral E.curve.left] [SmoothOfRelativeDimension 1 E.curve.hom]

/-- A smooth integral geometric generalized curve is a genuine Weierstrass DR object. -/
theorem exists_geometric_weierstrassIso :
    ∃ (W : WeierstrassCurve k) (hΔ : IsUnit W.Δ),
      Nonempty (E ≅ integralGeneralizedEllipticCurve W hΔ) := by
  obtain ⟨W, hΔ, e, he⟩ := exists_geometric_groupIso E
  let F := integralGeneralizedEllipticCurve W hΔ
  let _ : Smooth E.curve.hom := SmoothOfRelativeDimension.smooth 1 E.curve.hom
  let _ : Smooth F.curve.hom := integralCurveStructure_smooth W hΔ
  let _ := integralCurveGrpObj W hΔ
  let _ : IsMonHom e.hom := he
  exact ⟨W, hΔ, ⟨isoOfSmoothGroup E F e⟩⟩

end FLT.Mazur.GeneralizedEllipticCurve
