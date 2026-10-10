/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementNaturality
public import FLT.Mazur.SchemeAffineTestComparison

/-!
# Naturality of effective comparisons on affine tests

Coordinate normalization preserves the naturality square already proved
for the constructed common affine cross refinement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem conjugate_naturality {B : Type*} [Category B]
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : B}
    (e₀ : a₀ ≅ b₀) (e₁ : a₁ ≅ b₁) (q₀ : c₀ ≅ d₀) (q₁ : c₁ ≅ d₁)
    (f : a₀ ⟶ a₁) (g : b₀ ⟶ b₁) (j : c₀ ⟶ c₁) (k : d₀ ⟶ d₁)
    (t₀ : a₀ ⟶ c₀) (t₁ : a₁ ⟶ c₁)
    (hf : f ≫ e₁.hom = e₀.hom ≫ g) (hj : j ≫ q₁.hom = q₀.hom ≫ k)
    (ht : f ≫ t₁ = t₀ ≫ j) :
    g ≫ (e₁.inv ≫ t₁ ≫ q₁.hom) = (e₀.inv ≫ t₀ ≫ q₀.hom) ≫ k := by
  apply (cancel_epi e₀.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc e₀.hom g, ← hf]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc f t₁, ht, Category.assoc, hj]

variable {X Y : Scheme.{u}} {p : Y ⟶ X}
variable (C C' : Chart p) {A : CommRingCat.{u}}
variable (b : Spec A ⟶ Spec C.baseRing) (b' : Spec A ⟶ Spec C'.baseRing)
variable (w : b ≫ C.base = b' ≫ C'.base)
variable {M N : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (E : SchemeGeometricDescent.Data p N)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [((pullback C.cover).obj N).IsQuasicoherent]
variable [((pullback C'.cover).obj N).IsQuasicoherent]
attribute [local irreducible] sheaf map CrossRefinement.effectiveComparison pullbackCongr

/-- Affine test comparisons intertwine the descended maps on the original charts. -/
@[reassoc]
theorem affineTestComparison_naturality (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    (pullback b).map (C.map D E f hf) ≫ (C.affineTestComparison C' b b' w E).hom =
      (C.affineTestComparison C' b b' w D).hom ≫ (pullback b').map (C'.map D E f hf) := by
  unfold affineTestComparison
  exact conjugate_naturality
    ((pullbackCongr (Spec.map_preimage b)).app (C.sheaf D))
    ((pullbackCongr (Spec.map_preimage b)).app (C.sheaf E))
    ((pullbackCongr (Spec.map_preimage b')).app (C'.sheaf D))
    ((pullbackCongr (Spec.map_preimage b')).app (C'.sheaf E)) _ _ _ _ _ _
    ((pullbackCongr (Spec.map_preimage b)).hom.naturality (C.map D E f hf))
    ((pullbackCongr (Spec.map_preimage b')).hom.naturality (C'.map D E f hf))
    ((C.commonBaseCrossRefinement C' (Spec.preimage b) (Spec.preimage b')
      (by simpa only [Spec.map_preimage] using w)).effectiveComparison_naturality D E f hf)

end FLT.Mazur.SchemeAffineDescent.Chart
