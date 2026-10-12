/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneGroupProjectivePoint
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso

/-!
# Complete pointed presentations of original geometric generalized curves

The original smooth integral generalized curve is isomorphic, over its original
field and preserving its specified point, to a constructed nonsingular cubic.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (E : GeneralizedEllipticCurve (Spec (.of k)))
  [IsIntegral E.curve.left] [SmoothOfRelativeDimension 1 E.curve.hom]

/-- Every specified point gives a complete nonsingular pointed Weierstrass presentation. -/
theorem exists_geometric_point_projectiveIso (s : 𝟙_ (Over (Spec (.of k))) ⟶ E.curve) :
    ∃ (W : WeierstrassCurve k) (_ : W.IsElliptic) (e : E.curve.left ≅ integralCurve W),
      e.hom ≫ integralCurveStructure W = E.curve.hom ∧
        s.left ≫ e.hom = integralCurveZero W := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Smooth E.curve.hom := SmoothOfRelativeDimension.smooth 1 E.curve.hom
  let _ : IsIso E.inclusion := inclusion_isIso_of_smooth E
  let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  have h := E.family.genus.fiber k (𝟙 _) (𝟙 _) E.curve.hom IsPullback.of_id_fst
  let hI := (smoothSectionCartier E.curve.hom s.left inferInstance inferInstance s.w).1
  exact ⟨GenusOneGroupCoordinates.equation E.curve h.toNodalFiberCore.topologicalKrullDim_eq_one
      h.constantSections h.genus_one s hI,
    GenusOneGroupCoordinates.equation_isElliptic E.curve
      h.toNodalFiberCore.topologicalKrullDim_eq_one h.constantSections h.genus_one s hI,
    GenusOneGroupCoordinates.projectiveIso E.curve h.toNodalFiberCore.topologicalKrullDim_eq_one
      h.constantSections h.genus_one s hI,
    GenusOneGroupCoordinates.projectiveIso_over E.curve
      h.toNodalFiberCore.topologicalKrullDim_eq_one h.constantSections h.genus_one s hI,
    GenusOneGroupCoordinates.toProjective_point E.curve
      h.toNodalFiberCore.topologicalKrullDim_eq_one h.constantSections h.genus_one s hI⟩

/-- The actual identity is retained in a complete geometric Weierstrass presentation. -/
theorem exists_geometric_identity_projectiveIso :
    ∃ (W : WeierstrassCurve k) (_ : W.IsElliptic) (e : E.curve.left ≅ integralCurve W),
      e.hom ≫ integralCurveStructure W = E.curve.hom ∧
        E.identitySection.left ≫ e.hom = integralCurveZero W :=
  exists_geometric_point_projectiveIso E E.identitySection

end FLT.Mazur.GeneralizedEllipticCurve
