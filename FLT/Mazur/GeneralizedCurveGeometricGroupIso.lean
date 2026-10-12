/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneGroupProjectiveGroup
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso

/-!
# Group presentations of the actual geometric generalized curves

The original smooth group is isomorphic over the original field to the group
on the constructed nonsingular cubic. Its complete curve presentation retains
the original inclusion and identity.
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

/-- The original geometric smooth group has a constructed Weierstrass group presentation. -/
theorem exists_geometric_groupIso :
    ∃ (W : WeierstrassCurve k) (hΔ : IsUnit W.Δ)
      (e : E.group ≅ integralCurveOver W),
      let _ := integralCurveGrpObj W hΔ
      IsMonHom e.hom := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Smooth E.curve.hom := SmoothOfRelativeDimension.smooth 1 E.curve.hom
  let _ : IsIso E.inclusion := inclusion_isIso_of_smooth E
  let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  have h := E.family.genus.fiber k (𝟙 _) (𝟙 _) E.curve.hom IsPullback.of_id_fst
  let s := E.identitySection
  let hI := (smoothSectionCartier E.curve.hom s.left inferInstance inferInstance s.w).1
  let W := GenusOneGroupCoordinates.equation E.curve
    h.toNodalFiberCore.topologicalKrullDim_eq_one h.constantSections h.genus_one s hI
  let hΔ : IsUnit W.Δ := (GenusOneGroupCoordinates.equation_isElliptic E.curve
    h.toNodalFiberCore.topologicalKrullDim_eq_one h.constantSections h.genus_one s hI).isUnit
  let e := GenusOneGroupCoordinates.projectiveOverIso E.curve
    h.toNodalFiberCore.topologicalKrullDim_eq_one h.constantSections h.genus_one s hI
  refine ⟨W, hΔ, asIso E.inclusion ≪≫ e, ?_⟩
  let _ := integralCurveGrpObj W hΔ
  let _ : IsMonHom e.hom := GenusOneGroupCoordinates.projectiveOverIso_isMonHom E.curve
    h.toNodalFiberCore.topologicalKrullDim_eq_one h.constantSections h.genus_one s hI rfl
  let _ : IsMonHom (asIso E.inclusion).hom := isMonHom_ofIso (asIso E.inclusion)
  change IsMonHom ((asIso E.inclusion).hom ≫ e.hom)
  infer_instance

end FLT.Mazur.GeneralizedEllipticCurve
