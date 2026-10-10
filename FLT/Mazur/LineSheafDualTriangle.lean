/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafBidual

/-!
# The evaluation triangle for intrinsic sheaf duality

The intrinsic bidual satisfies the evaluation triangle. For line sheaves it
identifies the dual bidual map with inverse biduality, so every isomorphism
of dual lines comes from an actual isomorphism of the original lines.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
attribute [local irreducible] tensor moduleSheafBidual
variable {X : Scheme.{u}}

/-- Evaluation naturality, stated with sections of the actual dual sheaf. -/
lemma dualEvaluation_map_sections {M N : X.Modules} (a : M ⟶ N) (U : X.Opens)
    (φ : Γ(moduleSheafDual N, U)) (s : Γ(M, U)) :
    (moduleSheafDualEvaluation M).app U
        (pure _ _ U ((moduleSheafDualMap M a).app U φ) s) =
      (moduleSheafDualEvaluation N).app U (pure _ _ U φ (a.app U s)) := by
  simp only [moduleSheafDualEvaluation_pure, moduleSheafDualMap_app, moduleDualEval_precomp]

/-- Bidual evaluation, stated entirely using sections of the actual dual sheaf. -/
lemma dualEvaluation_bidual_sections (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (φ : Γ(moduleSheafDual M, U)) :
    (moduleSheafDualEvaluation (moduleSheafDual M)).app U
        (pure _ _ U ((moduleSheafBidual M).app U s) φ) =
      (moduleSheafDualEvaluation M).app U (pure _ _ U φ s) := by
  simp only [moduleSheafDualEvaluation_pure, moduleSheafBidual_eval]

/-- Morphisms to the actual dual are separated by their local evaluation pairings. -/
lemma dualEvaluation_hom_ext {M A : X.Modules} (a b : A ⟶ moduleSheafDual M)
    (h : ∀ (U : X.Opens) (x : Γ(A, U)) (s : Γ(M, U)),
      (moduleSheafDualEvaluation M).app U (pure _ _ U (a.app U x) s) =
        (moduleSheafDualEvaluation M).app U (pure _ _ U (b.app U x) s)) : a = b := by
  apply moduleSheafDual_hom_ext M A
  apply ModuleSheafTensor.hom_ext
  intro U x s
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure,
    Hom.id_app, ConcreteCategory.id_apply] using h U x s


/-- Evaluation of biduals satisfies the intrinsic duality triangle. -/
lemma moduleSheafBidual_dual_triangle (M : X.Modules) :
    moduleSheafBidual (moduleSheafDual M) ≫
      moduleSheafDualMap M (moduleSheafBidual M) = 𝟙 (moduleSheafDual M) := by
  apply dualEvaluation_hom_ext
  intro U φ s
  change (moduleSheafDualEvaluation M).app U
    (pure _ _ U ((moduleSheafDualMap M (moduleSheafBidual M)).app U
      ((moduleSheafBidual (moduleSheafDual M)).app U φ)) s) =
      (moduleSheafDualEvaluation M).app U (pure _ _ U φ s)
  rw [dualEvaluation_map_sections, dualEvaluation_bidual_sections,
    dualEvaluation_bidual_sections]


end FLT.Mazur.FCurve
