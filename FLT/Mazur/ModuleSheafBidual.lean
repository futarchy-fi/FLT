/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTensorInverseComparison

/-!
# The canonical morphism to the intrinsic double dual

Currying the transposed evaluation constructs the bidual map. Its pairing
is evaluation in the original order, and it is natural in the module sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleSheafTensorAssociator

attribute [local irreducible] ModuleSheafTensor.tensor

variable {X : Scheme.{u}}

/-- Transposed evaluation, curried into the actual intrinsic double dual. -/
def moduleSheafBidual (M : X.Modules) : M ⟶ moduleSheafDual (moduleSheafDual M) :=
  ModuleSheafTensorCurrying.homEquiv _ _ _
      ((comm M (moduleSheafDual M)).hom ≫ moduleSheafDualEvaluation M) ≫
    (moduleSheafDualInternalHomIso (moduleSheafDual M)).inv

/-- Pairing the bidual image with a functional evaluates that functional. -/
lemma moduleSheafBidual_eval (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (φ : Γ(moduleSheafDual M, U)) :
    moduleDualEval (moduleSheafDual M) U ((moduleSheafBidual M).app U s) φ =
      moduleDualEval M U φ s := by
  change moduleDualEval (moduleSheafDual M) U
    ((moduleSheafDualInternalHomIso (moduleSheafDual M)).inv.app U _) φ = _
  rw [moduleSheafDualInternalHomIso_inv_eval]
  change ((comm M (moduleSheafDual M)).hom ≫ moduleSheafDualEvaluation M).app U
    (pure M (moduleSheafDual M) U (M.presheaf.map (𝟙 U).op s) φ) = _
  simp only [op_id, M.presheaf.map_id, ConcreteCategory.id_apply,
    Hom.comp_app, ConcreteCategory.comp_apply, comm_hom_pure, moduleSheafDualEvaluation_pure]

/-- Pairing against the source separates morphisms into the intrinsic dual. -/
lemma moduleSheafDual_hom_ext (M A : X.Modules) {f g : A ⟶ moduleSheafDual M}
    (h : ModuleSheafTensor.map f (𝟙 M) ≫ moduleSheafDualEvaluation M =
      ModuleSheafTensor.map g (𝟙 M) ≫ moduleSheafDualEvaluation M) : f = g := by
  apply (cancel_mono (moduleSheafDualInternalHomIso M).hom).mp
  apply (ModuleSheafTensorCurrying.homEquiv A M (structureModule X)).symm.injective
  simpa only [ModuleSheafTensorCurrying.homEquiv_symm_precomp,
    moduleSheafDualEvaluation, moduleSheafDualInternalHomIso, asIso_hom] using h

/-- The canonical bidual construction commutes with every module-sheaf morphism. -/
@[reassoc]
lemma moduleSheafBidual_naturality {M N : X.Modules} (f : M ⟶ N) :
    moduleSheafBidual M ≫ moduleSheafDualMap (moduleSheafDual N) (moduleSheafDualMap M f) =
      f ≫ moduleSheafBidual N := by
  apply moduleSheafDual_hom_ext (moduleSheafDual N) M
  apply ModuleSheafTensor.hom_ext
  intro U s φ
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, ModuleSheafTensor.map_pure,
    Hom.id_app, ConcreteCategory.id_apply, moduleSheafDualEvaluation_pure,
    moduleSheafDualMap_app, moduleDualEval_precomp, moduleSheafBidual_eval]

end FLT.Mazur.FCurve
