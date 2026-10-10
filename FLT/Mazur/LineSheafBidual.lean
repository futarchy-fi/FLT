/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafBidual

/-!
# Canonical biduality for line sheaves

The evaluation-defined bidual map commutes with open restriction and is
invertible on each rank-one chart, hence on every locally free line sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor

attribute [local irreducible] ModuleSheafTensor.tensor

variable {X : Scheme.{u}}

/-- Biduality on the structure sheaf is the canonical unit duality twice. -/
lemma moduleSheafBidual_unit :
    moduleSheafBidual (structureModule X) = moduleSheafDualUnitIso.inv ≫
      moduleSheafDualMap _ (moduleSheafDualUnitIso (X := X)).hom := by
  apply moduleSheafDual_hom_ext
  apply ModuleSheafTensor.hom_ext
  intro U s φ
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, ModuleSheafTensor.map_pure,
    Hom.id_app, ConcreteCategory.id_apply, moduleSheafDualEvaluation_pure,
    moduleSheafBidual_eval, moduleSheafDualMap_app, moduleDualEval_precomp]
  change moduleDualEval (structureModule X) U φ s =
    moduleDualEval (structureModule X) U (moduleDualUnitSection U s)
      (moduleDualEval (structureModule X) U φ (1 : Γ(X, U)))
  rw [moduleDualEval_unitSection]
  simpa only [smul_eq_mul, mul_one] using
    (moduleDualEval (structureModule X) U φ).map_smul s (1 : Γ(X, U))

/-- The canonical bidual morphism respects the actual open-restriction comparisons. -/
lemma moduleSheafBidual_restrict (M : X.Modules) (U : X.Opens) :
    (restrictFunctor U.ι).map (moduleSheafBidual M) ≫
      (moduleSheafDualRestrictIso (moduleSheafDual M) U).hom =
    moduleSheafBidual (M.restrict U.ι) ≫
      moduleSheafDualMap _ (moduleSheafDualRestrictIso M U).hom := by
  apply moduleSheafDual_hom_ext
  apply ModuleSheafTensor.hom_ext
  intro W s φ
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, ModuleSheafTensor.map_pure,
    Hom.id_app, ConcreteCategory.id_apply, moduleSheafDualEvaluation_pure,
    moduleSheafDualMap_app, moduleDualEval_precomp, moduleSheafBidual_eval]
  change moduleDualEval ((moduleSheafDual M).restrict U.ι) W
    (moduleDualOpenSectionsEquiv (moduleSheafDual M) U W
      ((moduleSheafBidual M).app (U.ι ''ᵁ W) s)) φ =
    moduleDualEval (M.restrict U.ι) W (moduleDualOpenSectionsEquiv M U W φ) s
  rw [moduleDualOpenSectionsEquiv_eval, moduleSheafBidual_eval,
    moduleDualOpenSectionsEquiv_eval]

/-- A global trivialization makes the evaluation-defined bidual map invertible. -/
theorem moduleSheafBidual_isIso_of_trivial {M : X.Modules}
    (e : M ≅ structureModule X) : IsIso (moduleSheafBidual M) := by
  have : IsIso (moduleSheafBidual (structureModule X)) := by
    rw [moduleSheafBidual_unit]
    have : IsIso (moduleSheafDualMap _ (moduleSheafDualUnitIso (X := X)).hom) :=
      inferInstanceAs (IsIso (moduleSheafDualIso _ moduleSheafDualUnitIso).hom)
    infer_instance
  have : IsIso (moduleSheafDualMap (moduleSheafDual (structureModule X))
      (moduleSheafDualMap M e.hom)) :=
    inferInstanceAs (IsIso (moduleSheafDualIso _ (moduleSheafDualIso M e)).hom)
  have : IsIso (moduleSheafBidual M ≫ moduleSheafDualMap _ (moduleSheafDualMap M e.hom)) := by
    rw [moduleSheafBidual_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (moduleSheafDualMap _ (moduleSheafDualMap M e.hom))

/-- Canonical biduality is an isomorphism for every locally free rank-one sheaf. -/
theorem moduleSheafBidual_isIso {M : X.Modules} (hM : LocallyFreeRankOne M) :
    IsIso (moduleSheafBidual M) := by
  choose U hx e using hM
  apply ModuleSheafOpenIsoDetection.isIso_of_openCover (moduleSheafBidual M) U
    (fun x ↦ ⟨x, hx x⟩)
  intro x
  have := moduleSheafBidual_isIso_of_trivial (e x).some
  have : IsIso (moduleSheafDualMap _ (moduleSheafDualRestrictIso M (U x)).hom) :=
    inferInstanceAs (IsIso (moduleSheafDualIso _ (moduleSheafDualRestrictIso M (U x))).hom)
  have : IsIso ((restrictFunctor (U x).ι).map (moduleSheafBidual M) ≫
      (moduleSheafDualRestrictIso (moduleSheafDual M) (U x)).hom) := by
    rw [moduleSheafBidual_restrict]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (moduleSheafDualRestrictIso (moduleSheafDual M) (U x)).hom

/-- Canonical biduality, retaining its evaluation-defined morphism. -/
def lineSheafBidualIso {M : X.Modules} (hM : LocallyFreeRankOne M) :
    M ≅ moduleSheafDual (moduleSheafDual M) := by
  have := moduleSheafBidual_isIso hM
  exact asIso (moduleSheafBidual M)

end FLT.Mazur.FCurve
