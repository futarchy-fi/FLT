/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTildeSemilinearCoherence

/-!
# Naturality of affine semilinear sheaf maps

Commuting squares of original coefficient maps give commuting squares of
actual pullback sheaves. Equality is checked on original sections through
the two adjunction units.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineTildeSemilinearNaturality
open AffineTildePullbackSectionMap AffineIteratedPullbackSections
open AffineTildeSemilinearCoherence
attribute [local irreducible] Scheme.Modules.pullback AffineTildeSemilinearMap.map
attribute [local irreducible] moduleSpecΓFunctor specUnit unit
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {M M' : ModuleCat R} {N N' : ModuleCat S}

/-- Tilde sends the original coefficient section through the given module map. -/
lemma tilde_map_unit (a : M ⟶ M') (m : M) :
    moduleSpecΓFunctor.map ((tilde.functor R).map a)
        ((tilde.toTildeΓNatIso (R := R)).hom.app M m) =
      (tilde.toTildeΓNatIso (R := R)).hom.app M' (a m) :=
  (ConcreteCategory.congr_hom ((tilde.toTildeΓNatIso (R := R)).hom.naturality a) m).symm

/-- Pulling back a tilde morphism preserves its original-section formula. -/
lemma pullback_tilde_map_unit (a : M ⟶ M') (m : M) :
    moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map ((tilde.functor R).map a))
        (unit φ M m) = unit φ M' (a m) := by
  rw [original_unit_apply]
  erw [specUnit_naturality, tilde_map_unit, original_unit_apply]
  rfl

/-- A coefficient square is a square of actual affine pullback sheaves. -/
lemma map_square (a : M ⟶ M') (b : N ⟶ N')
    (g : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N)
    (g' : M' ⟶ (ModuleCat.restrictScalars φ.hom).obj N')
    (h : ∀ m : M, b (g m) = g' (a m)) :
    AffineTildeSemilinearMap.map φ M N g ≫ (tilde.functor S).map b =
      (pullback (Spec.map φ)).map ((tilde.functor R).map a) ≫
        AffineTildeSemilinearMap.map φ M' N' g' := by
  apply hom_ext φ M
  intro m
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  erw [semilinearMap_unit, tilde_map_unit, pullback_tilde_map_unit,
    semilinearMap_unit, h m]

end FLT.Mazur.AffineTildeSemilinearNaturality
