/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedDegreeZero
public import FLT.Mazur.IdealAdicCohomologyImage

/-!
# Structure-module quotients are actual closed-scheme functions

The ideal-action image on the structure module is the original ideal module.
Its cokernel comparison preserves the actual closed-immersion pullback.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.GlobalIdealPowerCompatibility
namespace FLT.Mazur.StructureIdealPowerQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- The ideal-action image on functions is the original ideal module. -/
def multipleIso : multiple I (structureModule X) ≅ idealModule I := by
  let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
  apply affineImageIso (inclusion I (structureModule X)) (idealModuleι I)
  intro U
  rw [inclusion_range]
  ext x
  change x ∈ I.ideal U • (⊤ : Ideal Γ(X, U.1)) ↔
    x ∈ Set.range ((idealModuleι I).app U.1)
  rw [idealModuleι_range, Ideal.smul_eq_mul, Ideal.mul_top]
  rfl

/-- The identification retains both inclusions in the original structure module. -/
@[reassoc]
lemma multipleIso_inclusion :
    (multipleIso I).hom ≫ idealModuleι I = inclusion I (structureModule X) := by
  unfold multipleIso
  exact affineImageIso_comp _ _ _

/-- The actual adic quotient of functions is the closed structure pushforward. -/
def quotientIso (n : ℕ) :
    IdealAdicQuotient.quotient I (structureModule X) n ≅
      (Scheme.Modules.pushforward (I ^ n).subschemeι).obj
        (structureModule (I ^ n).subscheme) :=
  cokernel.mapIso _ _ (multipleIso (I ^ n)) (Iso.refl _) (by
    simpa using (multipleIso_inclusion (I ^ n)).symm) ≪≫
      IdealAdicQuotient.idealQuotientCokernelIso (I ^ n)

/-- The comparison sends the original adic projection to actual geometric restriction. -/
@[reassoc]
lemma quotientIso_projection (n : ℕ) :
    IdealAdicQuotient.projection I (structureModule X) n ≫ (quotientIso I n).hom =
      idealQuotientMap (I ^ n) := by
  dsimp only [quotientIso, Iso.trans_hom]
  rw [← Category.assoc]
  change (cokernel.π _ ≫ (cokernel.mapIso _ _ _ _ _).hom) ≫ _ = _
  erw [cokernel.π_desc]
  exact IdealAdicQuotient.idealQuotientCokernelIso_projection (I ^ n)

/-- Vanishing in the adic quotient is exactly vanishing on the actual closed subscheme. -/
lemma projection_eq_zero_iff (n : ℕ) (x : Γ(X, ⊤)) :
    (IdealAdicQuotient.projection I (structureModule X) n).app ⊤ x = 0 ↔
      (I ^ n).subschemeι.app ⊤ x = 0 := by
  have h := congrArg (fun k ↦ k.app ⊤ x) (quotientIso_projection I n)
  change (quotientIso I n).hom.app ⊤
    ((IdealAdicQuotient.projection I (structureModule X) n).app ⊤ x) =
      (I ^ n).subschemeι.app ⊤ x at h
  rw [← h]
  exact (map_eq_zero_iff _
    (ModuleSubobjectCoverEquality.app_injective (quotientIso I n).hom ⊤)).symm

end FLT.Mazur.StructureIdealPowerQuotient
