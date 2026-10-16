/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Specified functions on an affine open as an actual spectrum morphism

The canonical affine presentation identifies the section map exactly, so
comparisons with geometric maps retain the original coefficient homomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineOpenSpectrumFunctions
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}} (V : X.affineOpens) {B : CommRingCat.{u}}
  (φ : Γ(X, V.1) ⟶ B)

/-- The morphism into the original open specified by its original section homomorphism. -/
def map : Spec B ⟶ V.1.toScheme := Spec.map φ ≫ V.2.isoSpec.inv

/-- Pullback on global functions retains precisely the specified homomorphism. -/
theorem map_appTop : (map V φ).appTop =
    V.1.topIso.hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
  rw [map, Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_inv_appTop, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]

/-- Composition with an affine target is the spectrum of the original composite functions. -/
theorem map_comp {A : CommRingCat.{u}} (f : V.1.toScheme ⟶ Spec A) :
    map V φ ≫ f = Spec.map ((Scheme.ΓSpecIso A).inv ≫ f.appTop ≫
      V.1.topIso.hom ≫ φ) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, map_appTop]
  apply (cancel_epi (Scheme.ΓSpecIso A).inv).mp
  rw [← Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc]

/-- Restricting an original global affine map uses the actual restriction of its functions. -/
theorem map_comp_inclusion {A : CommRingCat.{u}} (f : X ⟶ Spec A) :
    map V φ ≫ V.1.ι ≫ f = Spec.map ((Scheme.ΓSpecIso A).inv ≫ f.appTop ≫
      X.presheaf.map (homOfLE (show V.1 ≤ ⊤ from le_top)).op ≫ φ) := by
  rw [map_comp, Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop]
  simp only [Scheme.Opens.topIso, Category.assoc, Functor.mapIso_hom,
    ← Functor.map_comp_assoc]
  rfl

end FLT.Mazur.AffineOpenSpectrumFunctions
