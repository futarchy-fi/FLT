/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafLocalEndomorphisms
public import FLT.Mazur.ModuleSheafOpenIsoDetection

/-!
# The endomorphism sheaf of a line

Scalar multiplication identifies the actual internal endomorphism sheaf
of every locally free rank-one module with the structure module.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.ModuleSheafScalarEndomorphisms
open ModuleSheafInternalHom
variable {X : Scheme.{u}} {M N : X.Modules}

/-- Restrict a slice-site isomorphism to a smaller open. -/
def sliceIsoRestrict {U V : X.Opens} (i : V ⟶ U) (e : M.over U ≅ N.over U) :
    M.over V ≅ N.over V where
  hom := restrict M N i e.hom
  inv := restrict N M i e.inv
  hom_inv_id := by
    apply sections_ext
    intro W s
    exact congrArg (fun k ↦ app M M k ((Over.map i).obj W) s) e.hom_inv_id
  inv_hom_id := by
    apply sections_ext
    intro W s
    exact congrArg (fun k ↦ app N N k ((Over.map i).obj W) s) e.inv_hom_id

/-- The scalar map is invertible on each actual rank-one chart. -/
lemma scalarMap_restrict_isIso (U : X.Opens)
    (e : M.restrict U.ι ≅ structureModule U.toScheme) :
    IsIso ((restrictFunctor U.ι).map (scalarMap M)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective ((scalarMap M).app (U.ι ''ᵁ V))
  exact bijective_of_slice
    (sliceIsoRestrict (homOfLE (U.ι_image_le V)) (sliceTrivialization U e))

/-- Every endomorphism of a line sheaf is locally, and hence globally, a unique scalar. -/
theorem scalarMap_isIso (hM : LocallyFreeRankOne M) : IsIso (scalarMap M) := by
  choose U hx e using hM
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover (scalarMap M) U
    (fun x ↦ ⟨x, hx x⟩)
  intro x
  exact scalarMap_restrict_isIso (U x) (e x).some

/-- The intrinsic endomorphism sheaf comparison for any line sheaf. -/
def endomorphismSheafIso (hM : LocallyFreeRankOne M) :
    structureModule X ≅ sheaf M M := by
  let _ := scalarMap_isIso hM
  exact asIso (scalarMap M)

/-- The comparison has the original scalar multiplication as its forward morphism. -/
lemma endomorphismSheafIso_hom (hM : LocallyFreeRankOne M) :
    (endomorphismSheafIso hM).hom = scalarMap M := rfl

/-- Scalar classification holds on every open, without a global trivialization. -/
theorem scalarMap_app_bijective (hM : LocallyFreeRankOne M) (U : X.Opens) :
    Function.Bijective ((scalarMap M).app U) := by
  let _ := scalarMap_isIso hM
  exact ConcreteCategory.bijective_of_isIso ((scalarMap M).app U)

end FLT.Mazur.FCurve.ModuleSheafScalarEndomorphisms
