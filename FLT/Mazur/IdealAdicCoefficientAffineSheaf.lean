/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisFiniteCover
public import FLT.Mazur.IdealAdicClosedGradedSheaf

/-!
# The actual coefficient rings are sheaves on affine opens

Each homogeneous coefficient is an actual module sheaf. Compactness of the
affine basis therefore proves descent for their pointwise direct sum. In
particular, sheafification leaves the original coefficient charts unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open FLT.Mazur.IdealAdicQuotient FLT.Mazur.IdealAdicGradedSections
open FLT.Mazur.IdealAdicGradedClosedAction

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The actual degreewise quotient sheaves, restricted to the affine basis. -/
def coefficientPiecePresheaf (n : ℕ) : X.affineOpensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (AffineBasis.inclusion X).op ⋙ (idealGraded (J.comap f) n).presheaf

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y] in
/-- Every original homogeneous coefficient already satisfies affine descent. -/
lemma coefficientPiecePresheaf_isSheaf (n : ℕ) :
    Presheaf.IsSheaf (AffineBasis.topology X) (coefficientPiecePresheaf J f n) :=
  (AffineBasis.inclusion X).op_comp_isSheaf_of_isSheaf _ _ _
    (Scheme.Modules.isSheaf (idealGraded (J.comap f) n))

/-- The actual graded ring restrictions are the direct sum of the original restrictions. -/
def coefficientDirectSumIso :
    FiniteCoverDirectSum.presheaf (coefficientPiecePresheaf J f) ≅
      coefficientAffinePresheaf J f ⋙ coefficientForget :=
  NatIso.ofComponents (fun _ ↦ (AddEquiv.refl _).toAddCommGrpIso) (by
    intro U V i
    apply ConcreteCategory.hom_ext
    intro s
    induction s using DirectSum.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add s t hs ht => simp only [map_add, hs, ht]
    | of n s =>
      change DirectSum.map (fun n ↦
        ((idealGraded (J.comap f) n).presheaf.map (homOfLE i.unop.le).op).hom)
          (DirectSum.of _ n s) = restrict (J.comap f) V.unop.1
            (homOfLE i.unop.le) (of (J.comap f) U.unop.1 n s)
      rw [DirectSum.map_of, restrict_of]
      rfl)

omit [IsLocallyNoetherian Y] [IsAffine Y] in
/-- The original affine coefficient rings satisfy the sheaf condition before sheafification. -/
lemma coefficientAffinePresheaf_isSheaf :
    Presheaf.IsSheaf (AffineBasis.topology X) (coefficientAffinePresheaf J f) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat)]
  have h := (Presheaf.isSheaf_of_iso_iff (coefficientDirectSumIso J f)).mp
    (AffineBasis.directSum_isSheaf X _ (coefficientPiecePresheaf_isSheaf J f))
  exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).mp h

/-- The canonical map from original coefficient charts to glued sections is an isomorphism. -/
instance coefficientSheafificationUnit_isIso :
    IsIso (affineRingSheafificationUnit (coefficientAffinePresheaf J f)) := by
  let _ := isIso_toSheafify (AffineBasis.topology X) (coefficientAffinePresheaf_isSheaf J f)
  unfold affineRingSheafificationUnit
  infer_instance

/-- The original coefficient ring is canonically the glued sheaf's ring on an affine chart. -/
def coefficientChartIso (U : X.affineOpens) :
    (coefficientAffinePresheaf J f).obj (.op U) ≅
      (coefficientRingSheaf J f).obj.obj (.op U.1) :=
  asIso ((affineRingSheafificationUnit (coefficientAffinePresheaf J f)).app (.op U))

omit [IsLocallyNoetherian Y] [IsAffine Y] in
/-- The affine chart isomorphism retains the canonical associated-sheaf map. -/
lemma coefficientChartIso_hom (U : X.affineOpens) :
    (coefficientChartIso J f U).hom =
      (affineRingSheafificationUnit (coefficientAffinePresheaf J f)).app (.op U) := rfl

end FLT.Mazur.IdealAdicGradedPullback
