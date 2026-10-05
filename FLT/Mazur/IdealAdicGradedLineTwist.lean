/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedSequence
public import FLT.Mazur.IdealTwistSectionOpen

/-!
# Line twists of the actual associated-graded coefficients

The quotient of consecutive ideal modules, tensored with a line, is the
associated-graded coefficient of the actual image filtration on that line.
The comparison retains the quotient map from the ideal tensor.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility
open FLT.Mazur.CoherentIdealIntersection ModuleSheafTensor

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The actual inclusion of consecutive ideal modules. -/
def idealStep (n : ℕ) : idealModule (I ^ (n + 1)) ⟶ idealModule (I ^ n) :=
  idealMap (fun _ ↦ Ideal.pow_le_pow_right (Nat.le_succ n))

instance idealStep_mono (n : ℕ) : Mono (idealStep I n) :=
  inferInstanceAs (Mono (idealMap _))

/-- The n-th graded coefficient of the ideal itself. -/
def idealGraded (n : ℕ) : X.Modules := cokernel (idealStep I n)

instance idealGraded_coherent [IsLocallyNoetherian X] (n : ℕ) :
    (idealGraded I n).IsFinitePresentation := by
  have := idealModule_coherent (I ^ (n + 1))
  have := idealModule_coherent (I ^ n)
  exact coherent_cokernel (idealStep I n)

/-- For a line, its ideal tensor identifies with the actual ideal-action image. -/
def lineMultipleIso (L : X.Modules) (hL : LocallyFreeRankOne L) :
    tensor (idealModule I) L ≅ multiple I L := by
  have : Mono (scalarAction I L) := scalarAction_mono I hL
  have : Mono (onto I L) := mono_of_mono_fac (onto_inclusion I L)
  have : IsIso (onto I L) := isIso_of_mono_of_epi _
  exact asIso (onto I L)

/-- The image comparison uses the original scalar action. -/
@[reassoc (attr := simp)]
lemma lineMultipleIso_inclusion (L : X.Modules) (hL : LocallyFreeRankOne L) :
    (lineMultipleIso I L hL).hom ≫ inclusion I L = scalarAction I L :=
  onto_inclusion I L

variable [IsLocallyNoetherian X] (L : X.Modules) [L.IsFinitePresentation]
  (hL : LocallyFreeRankOne L)

/-- Tensoring the ideal inclusion agrees with the actual power-image transition. -/
@[reassoc]
lemma idealStep_lineMultipleIso (n : ℕ) :
    ModuleSheafTensor.map (idealStep I n) (𝟙 L) ≫
      (lineMultipleIso (I ^ n) L hL).hom =
        (lineMultipleIso (I ^ (n + 1)) L hL).hom ≫ powerStep I L n := by
  apply (cancel_mono (inclusion (I ^ n) L)).mp
  rw [Category.assoc, lineMultipleIso_inclusion, Category.assoc, transition_comp,
    lineMultipleIso_inclusion, scalarAction_eq_tensor_inclusion,
    scalarAction_eq_tensor_inclusion]
  rw [← Category.assoc, ← ModuleSheafTensor.map_comp]
  simp only [Category.id_comp, idealStep, idealMap_comp]

/-- The graded line coefficient is the line twist of the actual graded ideal. -/
def gradedLineTwistIso (n : ℕ) : graded I L n ≅ tensor (idealGraded I n) L := by
  let S := (ShortComplex.cokernelSequence (idealStep I n)).map
    (ModuleSheafTensorCurrying.tensoring L)
  let e : cokernel S.f ≅ graded I L n :=
    cokernel.mapIso S.f (powerStep I L n)
      (lineMultipleIso (I ^ (n + 1)) L hL) (lineMultipleIso (I ^ n) L hL)
      (idealStep_lineMultipleIso I L hL n)
  exact e.symm ≪≫ (cokernelIsCokernel S.f).coconePointUniqueUpToIso
    (ModuleLineTensorExact.shortExact _
      { exact := ShortComplex.cokernelSequence_exact (idealStep I n)
        mono_f := inferInstanceAs (Mono (idealStep I n)) } L hL).gIsCokernel

/-- The graded comparison preserves the actual quotient of the ideal tensor. -/
@[reassoc]
lemma gradedProjection_gradedLineTwistIso (n : ℕ) :
    (lineMultipleIso (I ^ n) L hL).hom ≫ cokernel.π (powerStep I L n) ≫
      (gradedLineTwistIso I L hL n).hom =
        ModuleSheafTensor.map (cokernel.π (idealStep I n)) (𝟙 L) := by
  dsimp [gradedLineTwistIso, graded]
  simp only [cokernel.π_desc_assoc, Category.assoc, Iso.hom_inv_id_assoc]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom _
    (ModuleLineTensorExact.shortExact _
      { exact := ShortComplex.cokernelSequence_exact (idealStep I n)
        mono_f := inferInstanceAs (Mono (idealStep I n)) } L hL).gIsCokernel WalkingParallelPair.one

end FLT.Mazur.IdealAdicQuotient
