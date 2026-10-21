/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodalFamilySmoothOpenDimension
public import FLT.Mazur.GeneralizedCurveBaseChange

/-!
# Every generalized elliptic curve has a dimension-one smooth group

The defining nodal geometric fibers determine the dimension of the actual
smooth open over affine bases. The specified smooth-group isomorphism and
an affine cover of the original base then give the result without new hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The original smooth group has relative dimension one over every affine coefficient spectrum. -/
theorem group_relativeDimension_spec {R : Type} [CommRing R]
    (E : GeneralizedEllipticCurve (Spec (.of R))) :
    SmoothOfRelativeDimension 1 E.group.hom := by
  let _ : Flat E.curve.hom := E.family.family.2.1
  have hd : SmoothOfRelativeDimension 1 (curveSmoothOpen E.curve).hom :=
    E.family.toNodalFamilyCore.fibers.smoothOpen_relativeDimension_spec
  let _ : IsIso E.smoothIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map E.smoothIso.hom))
  rw [← E.smoothIso.hom.w]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1) hd _

/-- The full smooth group of any original generalized curve has relative dimension one. -/
instance smoothGroup_relativeDimension {S : Scheme} (E : GeneralizedEllipticCurve S) :
    SmoothOfRelativeDimension 1 E.group.hom := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @SmoothOfRelativeDimension 1) S.affineCover
  intro i
  exact group_relativeDimension_spec (E.baseChange (S.affineCover.f i))

end FLT.Mazur.GeneralizedEllipticCurve
