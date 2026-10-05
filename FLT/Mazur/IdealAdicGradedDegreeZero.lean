/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedUnit
public import FLT.Mazur.IdealAdicGradedClosedTwist
public import FLT.Mazur.IdealQuotientExact
public import FLT.Mazur.ClosedPushforwardFull

/-!
# The degree-zero coefficient is the closed structure module

The comparison is built from the actual ideal quotient sequence and retains
its quotient map. Full faithfulness then identifies the descended degree-zero
coefficient with the structure module of the actual closed subscheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.CoherentIdealIntersection
open FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Use the same power instance as the original consecutive-power sheaves. -/
local instance idealGradedOriginalPow : Pow X.IdealSheafData ℕ :=
  Scheme.IdealSheafData.instPowNat

/-- Equal ideals have inverse actual ideal-inclusion maps. -/
@[irreducible] def idealGradedZeroTransport {J K : X.IdealSheafData} (h : J = K) :
    idealModule J ≅ idealModule K where
  hom := idealMap h.le
  inv := idealMap h.ge
  hom_inv_id := by
    apply (cancel_mono (idealModuleι J)).mp
    simp only [Category.assoc, idealMap_comp, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (idealModuleι K)).mp
    simp only [Category.assoc, idealMap_comp, Category.id_comp]

/-- Transport commutes with the actual ideal inclusion. -/
lemma idealGradedZeroTransport_inclusion {J K : X.IdealSheafData} (h : J = K) :
    (idealGradedZeroTransport h).hom ≫ idealModuleι K = idealModuleι J := by
  unfold idealGradedZeroTransport
  exact idealMap_comp h.le

/-- The first power comparison with the original power instance fixed at its source. -/
@[irreducible]
def idealGradedZeroSourceIso : idealModule (I ^ (0 + 1)) ≅ idealModule I :=
  idealGradedZeroTransport (J := I ^ (0 + 1)) (K := I) (pow_one I)

/-- The zeroth power comparison with the original power instance fixed at its source. -/
@[irreducible]
def idealGradedZeroTargetIso : idealModule (I ^ 0) ≅ structureModule X := by
  have : IsIso (idealModuleι (I ^ 0)) := by
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    infer_instance
  exact asIso (idealModuleι (I ^ 0))

/-- The zeroth-power comparison retains the original ideal inclusion. -/
lemma idealGradedZeroTargetIso_hom :
    (idealGradedZeroTargetIso I).hom = idealModuleι (I ^ 0) := by
  unfold idealGradedZeroTargetIso
  rfl

/-- Consecutive-power inclusion preserves the original ideal inclusion. -/
lemma idealStep_inclusion (n : ℕ) :
    idealStep I n ≫ idealModuleι (I ^ n) = idealModuleι (I ^ (n + 1)) :=
  idealMap_comp _

/-- The degree-zero inclusion square commutes before passing to cokernels. -/
lemma idealGradedZero_square :
    idealStep I 0 ≫ (idealGradedZeroTargetIso I).hom =
      (idealGradedZeroSourceIso I).hom ≫ idealModuleι I := by
  rw [idealGradedZeroTargetIso_hom, idealStep_inclusion]
  unfold idealGradedZeroSourceIso
  exact (idealGradedZeroTransport_inclusion (J := I ^ (0 + 1)) (pow_one I)).symm

/-- The zeroth graded cokernel agrees with the cokernel of the original ideal inclusion. -/
@[irreducible]
def idealGradedZeroCokernelIso : idealGraded I 0 ≅ cokernel (idealModuleι I) :=
  cokernel.mapIso _ _ (idealGradedZeroSourceIso I)
    (idealGradedZeroTargetIso I) (idealGradedZero_square I)

/-- The cokernel comparison preserves its actual projection. -/
@[reassoc]
lemma idealGradedZeroCokernelIso_projection :
    cokernel.π (idealStep I 0) ≫ (idealGradedZeroCokernelIso I).hom =
      (idealGradedZeroTargetIso I).hom ≫ cokernel.π (idealModuleι I) := by
  unfold idealGradedZeroCokernelIso
  exact cokernel.π_desc _ _ _

/-- The actual quotient sequence computes the cokernel of the ideal inclusion. -/
@[irreducible]
def idealQuotientCokernelIso : cokernel (idealModuleι I) ≅
    (pushforward I.subschemeι).obj (structureModule I.subscheme) :=
  (cokernelIsCokernel (idealModuleι I)).coconePointUniqueUpToIso
    (idealQuotientComplex_shortExact I).gIsCokernel

/-- The cokernel comparison preserves the actual quotient map. -/
@[reassoc]
lemma idealQuotientCokernelIso_projection :
    cokernel.π (idealModuleι I) ≫ (idealQuotientCokernelIso I).hom = idealQuotientMap I := by
  unfold idealQuotientCokernelIso
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _
    (idealQuotientComplex_shortExact I).gIsCokernel WalkingParallelPair.one

/-- Degree zero of the ideal graded sheaf is the actual closed structure pushforward. -/
def idealGradedZeroIso : idealGraded I 0 ≅
    (pushforward I.subschemeι).obj (structureModule I.subscheme) :=
  idealGradedZeroCokernelIso I ≪≫ idealQuotientCokernelIso I

/-- The degree-zero comparison carries the graded unit to the original quotient. -/
@[reassoc]
lemma idealGradedUnit_zeroIso :
    idealGradedUnit I ≫ (idealGradedZeroIso I).hom = idealQuotientMap I := by
  dsimp only [idealGradedUnit, idealGradedZeroIso, Iso.trans_hom]
  rw [Category.assoc, idealGradedZeroCokernelIso_projection_assoc,
    idealGradedZeroTargetIso_hom]
  change (idealPowerZeroIso I).inv ≫ (idealPowerZeroIso I).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  exact idealQuotientCokernelIso_projection I


variable [IsLocallyNoetherian X]

/-- The actual descended degree-zero coefficient is the closed structure module. -/
def closedIdealGradedZeroIso : closedIdealGraded I 0 ≅ structureModule I.subscheme :=
  (closedPushforwardFullyFaithful I.subschemeι).preimageIso
    (closedIdealGradedIso I 0 ≪≫ idealGradedZeroIso I)

/-- Pushing forward the closed comparison recovers the original ideal quotient comparison. -/
lemma pushforward_closedIdealGradedZeroIso :
    (pushforward I.subschemeι).mapIso (closedIdealGradedZeroIso I) =
      closedIdealGradedIso I 0 ≪≫ idealGradedZeroIso I :=
  (closedPushforwardFullyFaithful I.subschemeι).isoEquiv.apply_symm_apply _

end FLT.Mazur.IdealAdicQuotient
