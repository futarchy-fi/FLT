/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleOpenCohomologyRestriction
public import FLT.Mazur.ProjectiveLineStandardComparison
public import FLT.Mazur.ProjectiveSpaceReindex
public import FLT.Mazur.ProjectiveTwistCohomology

/-!
# Positive-degree cohomology of the glued projective line

Lift the two projective indices to the coefficient universe, use the existing
zero-twist computation, and transport genuine Ext cohomology back to the glued line.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.ProjectiveSpaceUniverseReindex
open ProjectiveSpace MvPolynomial
universe v w
variable (R : Type u) [CommRing R] {ι : Type v} {κ : Type w}
attribute [local instance] MvPolynomial.gradedAlgebra
/-- Renaming variables preserves the standard grading. -/
def renameGraded (e : ι → κ) : grading R ι →+*ᵍ grading R κ where
  __ := (rename e : MvPolynomial ι R →ₐ[R] MvPolynomial κ R).toRingHom
  map_mem := fun h ↦ h.rename_isHomogeneous

@[simp]
lemma renameGraded_apply (e : ι → κ) (p : MvPolynomial ι R) :
    renameGraded R e p = rename e p := rfl

/-- Inverse coordinate renamings compose to the graded identity. -/
lemma renameGraded_symm_comp (e : ι ≃ κ) :
    (renameGraded R e.symm).comp (renameGraded R e) = .id (grading R ι) := by
  ext i
  simp [renameGraded]

/-- A bijective renaming carries the irrelevant ideal onto the irrelevant ideal. -/
lemma renameGraded_irrelevant (e : ι ≃ κ) :
    HomogeneousIdeal.irrelevant (grading R κ) ≤
      (HomogeneousIdeal.irrelevant (grading R ι)).map (renameGraded R e) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn p hp
  have h := HomogeneousIdeal.mem_irrelevant_of_mem (grading R ι) hn
    (hp.rename_isHomogeneous (f := e.symm))
  have hm := Ideal.mem_map_of_mem (renameGraded R e).toRingHom h
  change p ∈ (HomogeneousIdeal.irrelevant (grading R ι)).toIdeal.map
    (renameGraded R e).toRingHom
  simpa using hm

/-- Lift the two projective coordinate indices to the coefficient universe. -/
def reindexIso : space R (Fin 2) ≅ space R (ULift.{u} (Fin 2)) where
  hom := Proj.map (renameGraded R (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2))
    (renameGraded_irrelevant R Equiv.ulift)
  inv := Proj.map (renameGraded R (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)))
    (renameGraded_irrelevant R Equiv.ulift.symm)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have he := renameGraded_symm_comp R (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))
    simp only [Equiv.symm_symm] at he
    simpa only [he] using Proj.map_id (𝒜 := grading R (Fin 2))
  inv_hom_id := by
    rw [← Proj.map_comp]
    simpa only [renameGraded_symm_comp] using Proj.map_id (𝒜 := grading R (ULift.{u} (Fin 2)))
end FLT.Mazur.ProjectiveSpaceUniverseReindex
namespace FLT.Mazur.ProjectiveLineCohomologyVanishing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open FCurve ProjectiveSpace
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem standard_twist_positive (q : ℕ) :
    Subsingleton (ModuleH (twistingSheaf K (ULift.{u} (Fin 2)) 0) (q + 1)) := by
  have hz := TwistCechCohomology.sheaf_isZero_homology_large K (ULift.{u} (Fin 2)) 0 (by simp) q
  let := ModuleCat.isZero_iff_subsingleton.mp hz
  exact (twistModuleHEquiv K (ULift.{u} (Fin 2)) 0 (q + 1)).surjective.subsingleton

theorem standard_structure_positive (q : ℕ) :
    Subsingleton (ModuleH (structureUnitModule (space K (ULift.{u} (Fin 2)))) (q + 1)) := by
  let := standard_twist_positive K q
  exact (moduleHIsoOfIso (twistingSheafZeroIso K (ULift.{u} (Fin 2)))
    (q + 1)).surjective.subsingleton

theorem structure_positive (q : ℕ) :
    Subsingleton (ModuleH (structureUnitModule (ProjectiveLine.scheme K)) (q + 1)) := by
  let := standard_structure_positive K q
  let iso := ProjectiveLine.standardIso K ≪≫ ProjectiveSpaceUniverseReindex.reindexIso K
  let e := moduleHIsoEquiv iso
    (structureUnitModule (space K (ULift.{u} (Fin 2)))) (q + 1)
  let := e.surjective.subsingleton
  exact (moduleHIsoOfIso (Scheme.Modules.restrictUnitIso iso.hom)
    (q + 1)).surjective.subsingleton

theorem h1_zero : Subsingleton (H1 (ProjectiveLine.toBase K)) :=
  structure_positive K 0
end FLT.Mazur.ProjectiveLineCohomologyVanishing
