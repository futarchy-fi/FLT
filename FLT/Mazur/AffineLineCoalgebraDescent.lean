/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleCoalgebraDescent
public import FLT.Mazur.FaithfullyFlatInvertible
public import FLT.Mazur.TildeInvertibleLocal

/-!
# Effective descent of invertible affine coalgebras

The coefficient module descended by comonadicity is invertible, so its tilde
is a line bundle. Morphisms descend functorially with their reconstruction
square. This is the coalgebra interface, not a scheme-level stack assertion.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.AffineModuleCoalgebraDescent

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.FaithfullyFlat)

/-- Invertibility of the coefficient descends along the faithfully flat map. -/
theorem descendedModule_invertible (D : Data φ) [Module.Invertible S D.A] :
    Module.Invertible R (descendedModule φ hφ D) := by
  let := φ.hom.toAlgebra
  have : Module.FaithfullyFlat R S := hφ
  have : Module.Invertible S (S ⊗[R] descendedModule φ hφ D) :=
    Module.Invertible.congr (coefficientIso φ hφ D).symm.toLinearEquiv
  exact invertible_of_faithfullyFlat (S := S)

/-- The actual descended sheaf is locally free of rank one. -/
theorem descendedSheaf_locallyFreeRankOne (D : Data φ) [Module.Invertible S D.A] :
    FCurve.LocallyFreeRankOne (descendedSheaf φ hφ D) := by
  have := descendedModule_invertible φ hφ D
  exact SchemePicard.tilde_locallyFreeRankOne (descendedModule φ hφ D)

/-- A compatible morphism descends to the coefficient modules. -/
def descendedModuleMap {D E : Data φ} (f : D ⟶ E) :
    descendedModule φ hφ D ⟶ descendedModule φ hφ E :=
  (descentEquivalence φ hφ).inverse.map f

/-- Reconstruction intertwines a descended morphism with its given coefficient map. -/
@[reassoc]
theorem coefficientIso_naturality {D E : Data φ} (f : D ⟶ E) :
    (ModuleCat.extendScalars φ.hom).map (descendedModuleMap φ hφ f) ≫
        (coefficientIso φ hφ E).hom =
      (coefficientIso φ hφ D).hom ≫ f.f := by
  exact congrArg (fun g ↦ g.f) ((descentEquivalence φ hφ).counitIso.hom.naturality f)

/-- The descended map of affine sheaves. -/
def descendedSheafMap {D E : Data φ} (f : D ⟶ E) :
    descendedSheaf φ hφ D ⟶ descendedSheaf φ hφ E :=
  (tilde.functor R).map (descendedModuleMap φ hφ f)

/-- Descent preserves the identity map. -/
@[simp]
theorem descendedSheafMap_id (D : Data φ) :
    descendedSheafMap φ hφ (𝟙 D) = 𝟙 (descendedSheaf φ hφ D) := by
  simp [descendedSheafMap, descendedModuleMap, descendedSheaf, descendedModule]

/-- Descent preserves composition of compatible maps. -/
@[simp]
theorem descendedSheafMap_comp {D E F : Data φ} (f : D ⟶ E) (g : E ⟶ F) :
    descendedSheafMap φ hφ (f ≫ g) =
      descendedSheafMap φ hφ f ≫ descendedSheafMap φ hφ g := by
  simp [descendedSheafMap, descendedModuleMap, descendedSheaf, descendedModule]

/-- A descended coefficient map is uniquely specified by its reconstruction square. -/
theorem descendedModuleMap_unique {D E : Data φ} (f : D ⟶ E)
    (g : descendedModule φ hφ D ⟶ descendedModule φ hφ E)
    (hg : (ModuleCat.extendScalars φ.hom).map g ≫ (coefficientIso φ hφ E).hom =
      (coefficientIso φ hφ D).hom ≫ f.f) : g = descendedModuleMap φ hφ f := by
  apply (descentEquivalence φ hφ).functor.map_injective
  apply Comonad.Coalgebra.Hom.ext
  apply (cancel_mono (coefficientIso φ hφ E).hom).mp
  exact hg.trans (coefficientIso_naturality φ hφ f).symm

end FLT.Mazur.AffineModuleCoalgebraDescent
