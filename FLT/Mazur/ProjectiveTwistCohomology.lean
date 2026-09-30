/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveTwistCechCohomologyTwist
public import FLT.Mazur.AffineCoverCohomology
public import FLT.Mazur.CoherentFreeSheaf
public import FLT.Mazur.FiniteCechCyclesScalars
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # Base-linear Ext cohomology of projective twists -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.FCurve FLT.Mazur.CechSheafHZero

universe u

namespace FLT.Mazur.ProjectiveSpace

open LocalizationDegree TwistGradedCech MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (ι : Type u) (d : ℤ) (q : ℕ)

/-- Standard chart trivializations give finite presentations of every twist. -/
instance twistingSheaf_isFinitePresentation : (twistingSheaf R ι d).IsFinitePresentation :=
  coherent_of_openCover (twistingSheaf R ι d) (chart R ι) (iSup_chart R ι) fun i ↦
    (SheafOfModules.isFinitePresentation (chart R ι i).toScheme.ringCatSheaf).prop_of_iso
      (twistingSheafRestrictIso R ι d i).symm
      (unitSheaf_isFinitePresentation (chart R ι i).toScheme)


/-- The explicit cycles have the same base action as coefficient multiplication. -/
def twistCechCyclesEquiv :
    finiteCechRingCycles (twistingSheaf R ι d) (chart R ι)
      (constantSection R ι ⊤) q ≃ₗ[R]
        ((sheafComplex R ι d).sc q).g.hom.ker where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := Subtype.ext (smul_eq_termScalar R ι d q r x.val).symm

/-- The cycle comparison identifies the actual boundary submodules. -/
lemma twistCechCyclesEquiv_boundaries :
    (finiteCechRingBoundaries (twistingSheaf R ι d) (chart R ι)
      (constantSection R ι ⊤) q).map (twistCechCyclesEquiv R ι d q).toLinearMap =
        ((sheafComplex R ι d).sc q).moduleCatToCycles.range := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, rfl⟩

/-- Categorical Cech cohomology and the computed module complex agree over the base. -/
def twistCechHomologyEquiv :
    letI := Module.compHom
      (CH (chart R ι) (moduleAbelianSheaf (twistingSheaf R ι d)) q)
      (constantSection R ι ⊤)
    CH (chart R ι) (moduleAbelianSheaf (twistingSheaf R ι d)) q ≃ₗ[R]
      (sheafComplex R ι d).homology q := by
  letI := Module.compHom
    (CH (chart R ι) (moduleAbelianSheaf (twistingSheaf R ι d)) q)
    (constantSection R ι ⊤)
  exact (finiteCechRingHomologyEquiv (twistingSheaf R ι d) (chart R ι)
    (constantSection R ι ⊤) q).trans
      ((Submodule.Quotient.equiv _ _ (twistCechCyclesEquiv R ι d q)
        (twistCechCyclesEquiv_boundaries R ι d q)).trans
        (((sheafComplex R ι d).sc q).moduleCatHomologyIso.symm.toLinearEquiv))

/-- The computed twisting complex calculates actual Ext cohomology over the base ring. -/
def twistModuleHEquiv :
    letI := Module.compHom (ModuleH (twistingSheaf R ι d) q) (constantSection R ι ⊤)
    (sheafComplex R ι d).homology q ≃ₗ[R] ModuleH (twistingSheaf R ι d) q := by
  letI := Module.compHom (ModuleH (twistingSheaf R ι d) q) (constantSection R ι ⊤)
  letI := Module.compHom
    (CH (chart R ι) (moduleAbelianSheaf (twistingSheaf R ι d)) q)
    (constantSection R ι ⊤)
  exact (twistCechHomologyEquiv R ι d q).symm.trans
    (affineCoverRingCechEquiv (twistingSheaf R ι d) (chart R ι)
      (fun i ↦ Proj.isAffineOpen_basicOpen (grading R ι) (MvPolynomial.X i)
        (isHomogeneous_X R i) (by decide))
      (iSup_chart R ι) (constantSection R ι ⊤) q)

/-- Every integer twist has finite actual cohomology in every degree over the base. -/
theorem twist_moduleH_finite [Finite ι] :
    letI := Module.compHom (ModuleH (twistingSheaf R ι d) q) (constantSection R ι ⊤)
    Module.Finite R (ModuleH (twistingSheaf R ι d) q) := by
  let _baseModule := Module.compHom (ModuleH (twistingSheaf R ι d) q) (constantSection R ι ⊤)
  let _finite := TwistCechCohomology.finiteSheafHomology R ι d q
  exact Module.Finite.equiv (twistModuleHEquiv R ι d q)

end FLT.Mazur.ProjectiveSpace
