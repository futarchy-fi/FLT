/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCoefficientAffineSheaf
public import FLT.Mazur.IdealAdicRelativeTilde

/-!
# The actual relative tensor algebras are sheaves on affine opens

Their additive presheaf is the restriction of the actual closed pullback
module. Consequently the original relative rings already satisfy descent,
and their canonical sheafification maps are affine chart isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open FLT.Mazur.IdealAdicGradedClosedAction

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The actual tensor restrictions identify with the actual closed pullback restrictions. -/
def relativeTildeAffineIso :
    relativeAffinePresheaf J f ⋙ coefficientForget ≅
      (AffineBasis.inclusion X).op ⋙ (relativeTildePushforward J f).presheaf :=
  NatIso.ofComponents (fun U ↦ (relativeTildeChartEquiv J f U.unop).toAddCommGrpIso) (by
    intro U V i
    apply ConcreteCategory.hom_ext
    intro t
    exact (relativeTildeChartEquiv_restrict J f (homOfLE i.unop.le) t).symm)

omit [IsLocallyNoetherian X] in
/-- The original relative tensor rings satisfy affine descent before sheafification. -/
lemma relativeAffinePresheaf_isSheaf :
    Presheaf.IsSheaf (AffineBasis.topology X) (relativeAffinePresheaf J f) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat)]
  have hs : Presheaf.IsSheaf (AffineBasis.topology X)
      ((AffineBasis.inclusion X).op ⋙ (relativeTildePushforward J f).presheaf) :=
    (AffineBasis.inclusion X).op_comp_isSheaf_of_isSheaf _ _ _
      (Scheme.Modules.isSheaf (relativeTildePushforward J f))
  have h := (Presheaf.isSheaf_of_iso_iff (relativeTildeAffineIso J f)).mpr hs
  exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).mp h

/-- The canonical map from the original relative tensors to glued affine sections is invertible. -/
instance relativeSheafificationUnit_isIso :
    IsIso (affineRingSheafificationUnit (relativeAffinePresheaf J f)) := by
  let _ := isIso_toSheafify (AffineBasis.topology X) (relativeAffinePresheaf_isSheaf J f)
  unfold affineRingSheafificationUnit
  infer_instance

/-- The original tensor ring is the glued relative ring on each affine open. -/
def relativeChartIso (U : X.affineOpens) :
    (relativeAffinePresheaf J f).obj (.op U) ≅
      (relativeRingSheaf J f).obj.obj (.op U.1) :=
  asIso ((affineRingSheafificationUnit (relativeAffinePresheaf J f)).app (.op U))

omit [IsLocallyNoetherian X] in
/-- The chart isomorphism uses the original associated-sheaf map. -/
lemma relativeChartIso_hom (U : X.affineOpens) :
    (relativeChartIso J f U).hom =
      (affineRingSheafificationUnit (relativeAffinePresheaf J f)).app (.op U) := rfl

/-- Both actual chart isomorphisms preserve the original quotient map. -/
lemma relativeChartIso_quotient (U : X.affineOpens) :
    (relativeChartIso J f U).hom ≫ (relativeSheafQuotient J f).hom.app (.op U.1) =
      (relativeAffineQuotient J f).app (.op U) ≫ (coefficientChartIso J f U).hom :=
  (NatTrans.congr_app (relativeSheafQuotient_chart J f) (.op U)).symm

end FLT.Mazur.IdealAdicGradedPullback
