/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTildeSemilinearCoherence

/-!
# Composition of actual sheaf morphisms from original sections

The composition law depends only on the original-section normalization.
The sheaf morphisms remain parameters, avoiding any need to expand their
construction when this criterion is applied to concrete coefficient rings.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.AffineTildeMorphismCoherence

open AffineTildeSemilinearMap AffineIteratedPullbackSections
open AffinePullbackComparisonSections AffineTildeSemilinearCoherence

attribute [local irreducible] compositeIso Scheme.Modules.pullback
attribute [local irreducible] AffineTildeSemilinearMap.map moduleSpecΓFunctor specUnit

variable {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ T) (χ : R ⟶ T)
variable (w : Spec.map ψ ≫ Spec.map φ = Spec.map χ)
variable (M : ModuleCat R) (N : ModuleCat S) (P : ModuleCat T)

attribute [local irreducible] AffineTildePullbackSectionMap.unit

/-- Any normalized sheaf morphism has the same pulled-back original-section formula. -/
lemma pullback_hom_unit (a : (pullback (Spec.map φ)).obj (tilde M) ⟶ tilde N)
    (a₀ : M → N)
    (ha : ∀ m, moduleSpecΓFunctor.map a (AffineTildePullbackSectionMap.unit φ M m) =
      (tilde.toTildeΓNatIso (R := S)).hom.app N (a₀ m)) (m : M) :
    (moduleSpecΓFunctor (R := T)).map ((pullback (Spec.map ψ)).map a)
        (specUnit ψ ((pullback (Spec.map φ)).obj (tilde M))
          (AffineTildePullbackSectionMap.unit φ M m)) =
      AffineTildePullbackSectionMap.unit ψ N (a₀ m) := by
  rw [specUnit_naturality ψ a, ha m]
  exact (original_unit_apply ψ N (a₀ m)).symm

/-- Composition follows from original sections for arbitrary actual sheaf morphisms. -/
lemma hom_comp
    (a : (pullback (Spec.map φ)).obj (tilde M) ⟶ tilde N)
    (b : (pullback (Spec.map ψ)).obj (tilde N) ⟶ tilde P)
    (c : (pullback (Spec.map χ)).obj (tilde M) ⟶ tilde P)
    (a₀ : M → N) (b₀ : N → P) (c₀ : M → P)
    (ha : ∀ m, moduleSpecΓFunctor.map a (AffineTildePullbackSectionMap.unit φ M m) =
      (tilde.toTildeΓNatIso (R := S)).hom.app N (a₀ m))
    (hb : ∀ n, moduleSpecΓFunctor.map b (AffineTildePullbackSectionMap.unit ψ N n) =
      (tilde.toTildeΓNatIso (R := T)).hom.app P (b₀ n))
    (hc : ∀ m, moduleSpecΓFunctor.map c (AffineTildePullbackSectionMap.unit χ M m) =
      (tilde.toTildeΓNatIso (R := T)).hom.app P (c₀ m))
    (h : ∀ m, b₀ (a₀ m) = c₀ m) :
    (compositeIso (Spec.map ψ) (Spec.map φ) (Spec.map χ) w (tilde M)).inv ≫
        (pullback (Spec.map ψ)).map a ≫ b = c := by
  apply AffineTildePullbackSectionMap.hom_ext χ M
  intro m
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  rw [compositeIso_inv_original_unit φ ψ χ w M m,
    pullback_hom_unit φ ψ M N a a₀ ha m, hb, hc, h]

end FLT.Mazur.AffineTildeMorphismCoherence
