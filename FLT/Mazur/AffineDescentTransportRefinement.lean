/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNamedRefinementReconstruction
public import FLT.Mazur.SchemeDescentPairTransport

/-!
# Refinement of reconstruction squares carrying descent transport

Refining a reconstruction square also refines its cross-cover transport. The
two covering maps are normalized separately and need only agree over the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.SheafPullbackPathComparison
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y T T' : Scheme.{u}} {p : Y ⟶ X} {M : Y.Modules} (D : Data p M)
variable (c₀ c₁ : T ⟶ Y) (w : c₀ ≫ p = c₁ ≫ p) (t : T' ⟶ T)
variable (d₀ d₁ : T' ⟶ Y) (h₀ : t ≫ c₀ = d₀) (h₁ : t ≫ c₁ = d₁)
variable (w' : d₀ ≫ p = d₁ ≫ p)

/-- The transport square after separately normalizing the two refined covering maps. -/
@[reassoc]
theorem transport_pullback_square :
    (pullback t).map (D.transport c₀ c₁ w).hom ≫ (comparison t c₁ d₁ h₁).hom.app M =
      (comparison t c₀ d₀ h₀).hom.app M ≫ (D.transport d₀ d₁ w').hom := by
  rw [← D.transport_pullback c₀ c₁ w t d₀ d₁ h₀ h₁ w']
  simp only [SchemeOverlapDiagonalChart.normalize, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]

end FLT.Mazur.SchemeGeometricDescent.Data

namespace FLT.Mazur.AffineDescentTransportRefinement
open AffineNamedRefinementReconstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (v : φ ≫ b = a ≫ ψ)
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {M : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M)
variable (c₀ c₁ : Spec S ⟶ Y) (w : c₀ ≫ p = c₁ ≫ p)
variable (d₀ d₁ : Spec S' ⟶ Y)
variable (h₀ : Spec.map b ≫ c₀ = d₀) (h₁ : Spec.map b ≫ c₁ = d₁)
variable (w' : d₀ ≫ p = d₁ ≫ p)
variable {A B : (Spec R).Modules}

/-- A reconstruction square carrying original descent transport survives affine refinement. -/
@[reassoc]
theorem reconstruction_transport
    (e₀ : (pullback (Spec.map φ)).obj A ≅ (pullback c₀).obj M)
    (e₁ : (pullback (Spec.map φ)).obj B ≅ (pullback c₁).obj M) (f : A ⟶ B)
    (hf : (pullback (Spec.map φ)).map f ≫ e₁.hom =
      e₀.hom ≫ (D.transport c₀ c₁ w).hom) :
    (pullback (Spec.map ψ)).map ((pullback (Spec.map a)).map f) ≫
        (chart φ ψ a b v c₁ d₁ h₁ e₁).hom =
      (chart φ ψ a b v c₀ d₀ h₀ e₀).hom ≫ (D.transport d₀ d₁ w').hom := by
  rw [chart_hom, chart_hom, ← Category.assoc,
    AffineRefinementPullback.reconstruction_naturality φ ψ a b v e₀ e₁ f
      (D.transport c₀ c₁ w).hom hf,
    Category.assoc, D.transport_pullback_square, ← Category.assoc]

end FLT.Mazur.AffineDescentTransportRefinement
