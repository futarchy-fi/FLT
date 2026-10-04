/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDualPullbackRestrict

/-!
# Duality for arbitrary line bundles

The canonical dual evaluation is invertible on a locally free rank-one sheaf.
The proof transports evaluation on the structure module to each trivializing
open and uses open-cover detection of isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.SchemePicard

open FCurve

variable {X : Scheme.{u}} {M : X.Modules}

/-- Dualizing a local trivialization gives a local trivialization of the dual. -/
theorem dual_locallyFreeRankOne (hM : LocallyFreeRankOne M) :
    LocallyFreeRankOne (moduleSheafDual M) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hM x
  exact ⟨U, hx, ⟨moduleSheafDualRestrictIso M U ≪≫
    (moduleSheafDualIso _ e).symm ≪≫ moduleSheafDualUnitIso⟩⟩

/-- Evaluation is invertible for a globally trivial line bundle. -/
theorem evaluation_isIso_of_trivial (e : M ≅ structureModule X) :
    IsIso (moduleSheafDualEvaluation M) := by
  have hunit : IsIso (moduleSheafDualEvaluation (structureModule X)) := by
    rw [moduleSheafDualEvaluation_unit]
    change IsIso ((ModuleSheafTensor.congr moduleSheafDualUnitIso (Iso.refl _)).hom ≫ _)
    infer_instance
  let a := ModuleSheafTensor.congr (moduleSheafDualIso M e) (Iso.refl M)
  let b := ModuleSheafTensor.congr (Iso.refl (moduleSheafDual (structureModule X))) e
  have : IsIso (a.hom ≫ moduleSheafDualEvaluation M) := by
    change IsIso (ModuleSheafTensor.map (moduleSheafDualMap M e.hom) (𝟙 M) ≫ _)
    rw [moduleSheafDualEvaluation_naturality]
    change IsIso (b.hom ≫ moduleSheafDualEvaluation (structureModule X))
    infer_instance
  exact IsIso.of_isIso_comp_left a.hom _

/-- Evaluation is invertible on every trivializing open. -/
theorem evaluation_restrict_isIso (U : X.Opens)
    (e : M.restrict U.ι ≅ structureModule U.toScheme) :
    IsIso ((restrictFunctor U.ι).map (moduleSheafDualEvaluation M)) := by
  have := evaluation_isIso_of_trivial e
  let a := ModuleSheafTensor.restrictIso (moduleSheafDual M) M U.ι
  let b := ModuleSheafTensor.congr (moduleSheafDualRestrictIso M U) (Iso.refl (M.restrict U.ι))
  have : IsIso ((restrictFunctor U.ι).map (moduleSheafDualEvaluation M) ≫
      (restrictUnitIso U.ι).hom) := by
    rw [← moduleSheafDualEvaluation_restrict]
    change IsIso (a.hom ≫ b.hom ≫ moduleSheafDualEvaluation (M.restrict U.ι))
    infer_instance
  exact IsIso.of_isIso_comp_right _ (restrictUnitIso U.ι).hom

/-- The actual evaluation map of an arbitrary line bundle is an isomorphism. -/
theorem evaluation_isIso (hM : LocallyFreeRankOne M) :
    IsIso (moduleSheafDualEvaluation M) := by
  choose U hx he using hM
  exact ModuleSheafOpenIsoDetection.isIso_of_openCover _ U
    (fun x ↦ ⟨x, hx x⟩) (fun x ↦ evaluation_restrict_isIso (U x) (he x).some)

/-- Contraction identifies a line bundle tensored with its dual with the unit. -/
def evaluationIso (hM : LocallyFreeRankOne M) :
    ModuleSheafTensor.tensor (moduleSheafDual M) M ≅ structureModule X := by
  letI := evaluation_isIso hM
  exact asIso (moduleSheafDualEvaluation M)

/-- The contraction isomorphism is the canonical evaluation, not a chosen trivialization. -/
@[simp]
theorem evaluationIso_hom (hM : LocallyFreeRankOne M) :
    (evaluationIso hM).hom = moduleSheafDualEvaluation M := rfl

end FLT.Mazur.SchemePicard
