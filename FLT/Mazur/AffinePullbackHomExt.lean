/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionsReconstruction

/-!
# Detecting morphisms out of affine pullbacks on unit sections

Adjunction and affine quasi-coherent reconstruction reduce equality of maps
out of a pullback to their values on pulled-back global sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffinePullbackHomExt
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B : CommRingCat.{u}} (φ : A ⟶ B)
variable (M : (Spec A).Modules) [M.IsQuasicoherent] (N : (Spec B).Modules)

/-- Morphisms out of an affine quasi-coherent pullback are determined on unit sections. -/
theorem hom_ext (f g : (pullback (Spec.map φ)).obj M ⟶ N)
    (h : ∀ n : moduleSpecΓFunctor.obj M,
      f.app ⊤ (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ n) =
        g.app ⊤ (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ n)) :
    f = g := by
  apply ((pullbackPushforwardAdjunction (Spec.map φ)).homEquiv M N).injective
  apply AffineSectionsReconstruction.map_injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro n
  exact h n

end FLT.Mazur.AffinePullbackHomExt
