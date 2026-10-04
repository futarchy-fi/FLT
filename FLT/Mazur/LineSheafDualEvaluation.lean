/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDualPullbackRestrict

/-!
# The tensor inverse of a line sheaf

The intrinsic dual evaluation is invertible for every locally free rank-one
module sheaf. The proof checks the actual pairing on a trivializing open cover.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor

variable {X : Scheme.{u}} {M : X.Modules}

/-- The intrinsic dual of a line sheaf is again locally free of rank one. -/
theorem LocallyFreeRankOne.dual (hM : LocallyFreeRankOne M) :
    LocallyFreeRankOne (moduleSheafDual M) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hM x
  exact ⟨U, hx, ⟨moduleSheafDualRestrictIso M U ≪≫
    (moduleSheafDualIso _ e).symm ≪≫ moduleSheafDualUnitIso⟩⟩

/-- Evaluation is invertible for a globally trivial line. -/
theorem moduleSheafDualEvaluation_isIso_of_trivial (e : M ≅ structureModule X) :
    IsIso (moduleSheafDualEvaluation M) := by
  have : IsIso (moduleSheafDualEvaluation (structureModule X)) := by
    rw [moduleSheafDualEvaluation_unit]
    exact inferInstanceAs (IsIso ((congr moduleSheafDualUnitIso (Iso.refl _)).hom ≫
      (leftUnitor (structureModule X)).hom))
  have : IsIso (moduleSheafDualMap M e.hom) :=
    inferInstanceAs (IsIso (moduleSheafDualIso M e).hom)
  have : IsIso (map (moduleSheafDualMap M e.hom) (𝟙 M)) :=
    inferInstanceAs (IsIso (congr (moduleSheafDualIso M e) (Iso.refl M)).hom)
  have : IsIso (map (𝟙 (moduleSheafDual (structureModule X))) e.hom) :=
    inferInstanceAs (IsIso (congr (Iso.refl _) e).hom)
  have h := moduleSheafDualEvaluation_naturality M e.hom
  have : IsIso (map (moduleSheafDualMap M e.hom) (𝟙 M) ≫
      moduleSheafDualEvaluation M) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (map (moduleSheafDualMap M e.hom) (𝟙 M)) _

/-- The actual dual evaluation is an isomorphism for every line sheaf. -/
theorem moduleSheafDualEvaluation_isIso (hM : LocallyFreeRankOne M) :
    IsIso (moduleSheafDualEvaluation M) := by
  choose U hx e using hM
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover (moduleSheafDualEvaluation M) U
    (fun x ↦ ⟨x, hx x⟩)
  intro x
  have := moduleSheafDualEvaluation_isIso_of_trivial (e x).some
  have : IsIso (map (moduleSheafDualRestrictIso M (U x)).hom (𝟙 (M.restrict (U x).ι))) :=
    inferInstanceAs (IsIso
      (congr (moduleSheafDualRestrictIso M (U x)) (Iso.refl (M.restrict (U x).ι))).hom)
  have : IsIso ((restrictFunctor (U x).ι).map (moduleSheafDualEvaluation M) ≫
      (restrictUnitIso (U x).ι).hom) := by
    rw [← moduleSheafDualEvaluation_restrict]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (restrictUnitIso (U x).ι).hom

/-- The canonical tensor inverse, with no global trivialization hypothesis. -/
def lineSheafDualEvaluationIso (hM : LocallyFreeRankOne M) :
    tensor (moduleSheafDual M) M ≅ structureModule X := by
  have := moduleSheafDualEvaluation_isIso hM
  exact asIso (moduleSheafDualEvaluation M)

end FLT.Mazur.FCurve
