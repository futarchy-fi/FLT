/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SurjectiveStructureSupport
public import FLT.Mazur.CoherentComparisonLocus
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Detecting a finite comparison through its structure direct image

The canonical structure map is injective for a schematically dominant map.
It is invertible on every open where the original scheme map is invertible.
For an affine map, invertibility of this module map recovers the original scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.StructureDirectImage
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The structure comparison is invertible over an unchanged target open. -/
theorem unitMap_restrict_isIso (U : Y.Opens) [IsIso (f ∣_ U)] :
    IsIso ((restrictFunctor U.ι).map (unitMap f)) := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro V
  have h : IsIso ((f ∣_ U).app V) := inferInstance
  rw [morphismRestrict_app] at h
  let _ : IsIso (f.app (U.ι ''ᵁ V)) := IsIso.of_isIso_comp_right _
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso (f.app (U.ι ''ᵁ V))

/-- The comparison cokernel has no support on an unchanged target open. -/
theorem unitMap_cokernel_support_subset (U : Y.Opens) [IsIso (f ∣_ U)] :
    FCurve.CoherentDevissage.support (cokernel (unitMap f)) ⊆ (U : Set Y)ᶜ := by
  let _ := unitMap_restrict_isIso f U
  have hz : IsZero ((cokernel (unitMap f)).restrict U.ι) :=
    (PreservesCokernel.iso (restrictFunctor U.ι) (unitMap f)).isZero_iff.mpr
      (isZero_cokernel_of_epi _)
  intro y hy hU
  exact (FCurve.CoherentDevissage.isZero_restrict_iff _ U).mp hz y hU hy

/-- An affine scheme map is recovered from its canonical structure-module comparison. -/
theorem isIso_of_unitMap [IsAffineHom f] [IsIso (unitMap f)] : IsIso f := by
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms Scheme)
      _ (iSup_affineOpens_eq_top Y)]
  intro U
  have h := ConcreteCategory.bijective_of_isIso ((unitMap f).app U.1)
  let _ : IsIso (f.app U.1) := (ConcreteCategory.isIso_iff_bijective _).mpr h
  exact (isIso_morphismRestrict_iff_isIso_app f U.2).mpr inferInstance

end FLT.Mazur.StructureDirectImage
