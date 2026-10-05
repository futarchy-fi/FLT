/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicQuotient
public import FLT.Mazur.IdealTwistSectionOpen
public import FLT.Mazur.ClosedLineProjectionFormula
public import FLT.Mazur.IdealQuotientExact

/-!
# Ideal-adic line quotients on the actual closed subschemes

For a line sheaf, the quotient by the ideal-action image is the closed
pushforward of its pullback. The comparison carries the original quotient
projection to the pullback adjunction unit, retaining the restriction map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open ModuleSheafTensor

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}}
  (I : X.IdealSheafData) (L : X.Modules)
  (hL : LocallyFreeRankOne L)

/-- The line quotient is the tensor of the closed structure sheaf with the line. -/
def lineQuotientTensorIso (n : ℕ) :
    quotient I L n ≅ tensor
      ((pushforward (I ^ n).subschemeι).obj (structureModule (I ^ n).subscheme)) L := by
  have : Mono (scalarAction (I ^ n) L) := scalarAction_mono _ hL
  have : IsIso (onto (I ^ n) L) := by
    have : Mono (onto (I ^ n) L) := mono_of_mono_fac (onto_inclusion (I ^ n) L)
    exact isIso_of_mono_of_epi _
  let S := (idealQuotientComplex (I ^ n)).map (ModuleSheafTensorCurrying.tensoring L)
  let e : cokernel S.f ≅ quotient I L n :=
    cokernel.mapIso S.f (inclusion (I ^ n) L) (asIso (onto (I ^ n) L))
      (leftUnitor L) (by
        exact ((onto_inclusion (I ^ n) L).trans
          (scalarAction_eq_tensor_inclusion (I ^ n) L)).symm)
  exact e.symm ≪≫ (cokernelIsCokernel S.f).coconePointUniqueUpToIso
    (ModuleLineTensorExact.shortExact _ (idealQuotientComplex_shortExact (I ^ n)) L hL).gIsCokernel

/-- The tensor comparison retains the actual quotient projection. -/
@[reassoc]
lemma projection_lineQuotientTensorIso (n : ℕ) :
    projection I L n ≫ (lineQuotientTensorIso I L hL n).hom =
      (leftUnitor L).inv ≫ ModuleSheafTensor.map (idealQuotientMap (I ^ n)) (𝟙 L) := by
  dsimp [projection, lineQuotientTensorIso, quotient]
  simp only [cokernel.π_desc_assoc, Category.assoc, Iso.cancel_iso_inv_left]
  apply IsColimit.comp_coconePointUniqueUpToIso_hom _
    (ModuleLineTensorExact.shortExact _ (idealQuotientComplex_shortExact (I ^ n)) L hL).gIsCokernel
    WalkingParallelPair.one

/-- The quotient line is the direct image of its actual closed restriction. -/
def lineQuotientClosedIso (n : ℕ) :
    quotient I L n ≅ (pushforward (I ^ n).subschemeι).obj
      ((Scheme.Modules.pullback (I ^ n).subschemeι).obj L) :=
  lineQuotientTensorIso I L hL n ≪≫
    (ClosedLineProjectionFormula.projectionIso (I ^ n).subschemeι
      (structureModule (I ^ n).subscheme) L hL).symm ≪≫
    (pushforward (I ^ n).subschemeι).mapIso (leftUnitor _)

/-- The closed comparison sends projection to the canonical restriction unit. -/
@[reassoc]
lemma projection_lineQuotientClosedIso (n : ℕ) :
    projection I L n ≫ (lineQuotientClosedIso I L hL n).hom =
      (pullbackPushforwardAdjunction (I ^ n).subschemeι).unit.app L := by
  dsimp only [lineQuotientClosedIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [projection_lineQuotientTensorIso_assoc]
  apply (cancel_epi (leftUnitor L).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply ModuleSheafTensor.hom_ext
  intro U r l
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, ClosedLineProjectionFormula.projectionIso_inv,
    ClosedLineProjectionFormula.comparison_pure, pushforward_map_app]
  simp only [structureModule, leftUnitor_pure]
  erw [leftUnitor_pure]
  exact (((pullbackPushforwardAdjunction (I ^ n).subschemeι).unit.app L).val.app
    (op U)).hom.map_smul r l |>.symm

end FLT.Mazur.IdealAdicQuotient
