/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneGroupAffineChart
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso

/-!
# Geometric affine charts for original smooth generalized curves

The actual family contract supplies constant functions and genus one. Smoothness
identifies the whole curve with its specified group, so the coordinate construction
applies directly on the original point complement, including the original identity.
Relative spreading and extension across that point remain separate obligations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (E : GeneralizedEllipticCurve (Spec (.of k)))
  [IsIntegral E.curve.left] [SmoothOfRelativeDimension 1 E.curve.hom]

/-- Every specified point complement of the original geometric curve has an actual cubic chart. -/
theorem exists_geometric_point_affineChart (s : 𝟙_ (Over (Spec (.of k))) ⟶ E.curve) :
    ∃ (W : WeierstrassCurve k)
      (e : (Scheme.Opens.toScheme (X := E.curve.left) s.left.ker.support.compl) ≅
        Spec (.of W.toAffine.CoordinateRing)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k W.toAffine.CoordinateRing)) =
        (Scheme.Opens.ι (X := E.curve.left) s.left.ker.support.compl) ≫ E.curve.hom := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Smooth E.curve.hom := SmoothOfRelativeDimension.smooth 1 E.curve.hom
  let _ : IsIso E.inclusion := inclusion_isIso_of_smooth E
  let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
  have h := E.family.genus.fiber k (𝟙 _) (𝟙 _) E.curve.hom IsPullback.of_id_fst
  let hI := (smoothSectionCartier E.curve.hom s.left inferInstance inferInstance s.w).1
  exact ⟨GenusOneGroupCoordinates.equation E.curve h.toNodalFiberCore.topologicalKrullDim_eq_one
      h.constantSections h.genus_one s hI,
    GenusOneGroupCoordinates.affineIso E.curve h.toNodalFiberCore.topologicalKrullDim_eq_one
      h.constantSections h.genus_one s hI,
    GenusOneGroupCoordinates.affineIso_over E.curve
      h.toNodalFiberCore.topologicalKrullDim_eq_one h.constantSections h.genus_one s hI⟩

/-- The original identity complement has a constructed Weierstrass chart over its original field. -/
theorem exists_geometric_identity_affineChart :
    ∃ (W : WeierstrassCurve k)
      (e : (Scheme.Opens.toScheme (X := E.curve.left)
        E.identitySection.left.ker.support.compl) ≅ Spec (.of W.toAffine.CoordinateRing)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k W.toAffine.CoordinateRing)) =
        (Scheme.Opens.ι (X := E.curve.left) E.identitySection.left.ker.support.compl) ≫
          E.curve.hom :=
  exists_geometric_point_affineChart E E.identitySection

end FLT.Mazur.GeneralizedEllipticCurve
