/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSheafSectionCoordinates

/-!
# Generator normalization of recovered affine free coordinates

The affine tilde section isomorphism is the concrete realization of a
finite-support coefficient vector using the actual free sheaf generators.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFreeSheafCoordinates
open AffineModuleGlobalSections FreeSheafSectionCoordinates FCurve
variable (S : Scheme.{u}) [IsAffine S]

/-- The affine section isomorphism sends a basis vector to its canonical generator. -/
lemma sectionIso_single_one {ι : Type u} (i : ι) :
    (sectionIso S ι).hom (Finsupp.single i (1 : Γ(S, ⊤))) =
      (show structureModule S ⟶ SheafOfModules.free ι from
        SheafOfModules.ιFree i).app ⊤ (1 : Γ(S, ⊤)) := by
  rw [sectionIso_apply]
  change (ModuleGlobalEvaluationPullback.freeIso S.isoSpec.hom ι).hom.app ⊤
    (((pullback S.isoSpec.hom).map (tildeFinsupp ι).hom).app ⊤
      (pullGlobal S.isoSpec.hom _ (tilde.toOpen _ ⊤ (Finsupp.single i 1)))) = _
  rw [pullGlobal_naturality, tildeFinsupp_single_one, pull_generator]

/-- The abstract affine section isomorphism equals the concrete realization map. -/
lemma sectionIso_hom_eq_realize (ι : Type u) :
    (sectionIso S ι).hom.hom = realize S ι := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext_ring
  change (sectionIso S ι).hom (Finsupp.single i 1) =
    realize S ι (Finsupp.single i 1)
  rw [realize_single, one_smul]
  exact sectionIso_single_one S i

/-- Realization is a linear equivalence on every affine scheme. -/
def realizationEquiv (ι : Type u) :
    (ι →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] Γ((SheafOfModules.free ι : S.Modules), ⊤) :=
  (sectionIso S ι).toLinearEquiv

/-- The canonical realization is injective on an affine scheme. -/
lemma realize_injective (ι : Type u) : Function.Injective (realize S ι) := by
  rw [← sectionIso_hom_eq_realize]
  exact (sectionIso S ι).toLinearEquiv.injective

attribute [local irreducible] sectionIso coordinatesIso

/-- Recovered affine coordinates act on the realized actual sections. -/
lemma realize_coordinates {ι κ : Type u}
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (v : ι →₀ Γ(S, ⊤)) :
    realize S κ (coordinates S e v) = (sections S).map e.hom (realize S ι v) := by
  rw [← sectionIso_hom_eq_realize, ← sectionIso_hom_eq_realize]
  exact ConcreteCategory.congr_hom (sectionIso_coordinates_hom S e) v

end FLT.Mazur.AffineFreeSheafCoordinates
