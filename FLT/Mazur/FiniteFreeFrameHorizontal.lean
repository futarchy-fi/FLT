/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackRestrictionHorizontal
public import FLT.Mazur.FiniteFreePullbackFrame

/-!
# Successive pullbacks of original restricted frames

The original restriction-pullback comparisons preserve the finite free frame
through two consecutive base morphisms, including the ambient comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FiniteFreePullbackFrame
open FCurve
variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
variable (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (f' : Y₀ ⟶ Y₁) (g' : Y₁ ⟶ Y₂)
variable (i : Y₀ ⟶ X₀) (j : Y₁ ⟶ X₁) (k : Y₂ ⟶ X₂)
variable [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k]
variable (hf : i ≫ f = f' ≫ j) (hg : j ≫ g = g' ≫ k)
variable (M : X₂.Modules) {ι : Type u} (e : M.restrict k ≅ SheafOfModules.free ι)

/-- The actual comparison on the twice-pulled ambient sheaf preserves its original frame. -/
lemma frame_horizontal :
    (restrictFunctor i).mapIso ((pullbackComp f g).app M) ≪≫
        modulePullbackRestrictIso (f ≫ g) (f' ≫ g') i k
          (by rw [← Category.assoc, hf, Category.assoc, hg, Category.assoc]) M ≪≫
        frame (f' ≫ g') e =
      modulePullbackRestrictIso f f' i j hf ((pullback g).obj M) ≪≫
        frame f' (modulePullbackRestrictIso g g' j k hg M ≪≫ frame g' e) := by
  rw [← Iso.trans_assoc, modulePullbackRestrictIso_horizontal f g f' g' i j k hf hg]
  rw [Iso.trans_assoc, Iso.trans_assoc, frame_comp]
  apply Iso.ext
  simp only [frame, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

end FLT.Mazur.FiniteFreePullbackFrame
