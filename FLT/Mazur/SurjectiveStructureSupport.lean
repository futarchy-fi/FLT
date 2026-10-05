/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBranchDifferenceSheaf
public import FLT.Mazur.CoherentGenericCoordinates
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Support of a surjective structure-sheaf direct image

Over a reduced target, a quasi-compact dominant morphism injects the structure
module into its direct image. Thus that direct image has full support.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.AnnihilatorSubsheaf
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.StructureDirectImage

variable {X Y : Scheme.{u}}

/-- The structure module is nonzero at every point of a scheme. -/
theorem support_structureModule (X : Scheme.{u}) : support (structureModule X) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x hx
  have h : Subsingleton ((structureModule X).presheaf.stalk x) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hx
  have : Subsingleton (X.presheaf.stalk x) :=
    (structureStalkLinearEquiv x).symm.injective.subsingleton
  exact (zero_ne_one : (0 : X.presheaf.stalk x) ≠ 1) (Subsingleton.elim _ _)

/-- Scheme-theoretic dominance gives the actual structure-module monomorphism. -/
instance unitMap_mono (f : X ⟶ Y) [QuasiCompact f] [IsSchemeTheoreticallyDominant f] :
    Mono (unitMap f) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  exact f.app_injective U.unop

/-- Dominance over a reduced target gives full support for the structure direct image. -/
theorem support_eq_univ_of_dominant (f : X ⟶ Y) [QuasiCompact f] [IsDominant f]
    [IsReduced Y] : support ((pushforward f).obj (structureModule X)) = Set.univ := by
  have := IsSchemeTheoreticallyDominant.of_isDominant f
  apply Set.eq_univ_of_univ_subset
  rw [← support_structureModule Y]
  exact support_subset_of_mono (unitMap f)

end FLT.Mazur.StructureDirectImage
