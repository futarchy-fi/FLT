/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTildePullbackSectionMap
public import FLT.Mazur.AffinePullbackComparisonSections

/-!
# Composition of normalized affine coefficient sheaf maps

Equality on original coefficient sections proves the sheaf-level composition
law, including the canonical comparison between the two pullbacks.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.AffineTildeSemilinearCoherence

open AffineTildeSemilinearMap AffineIteratedPullbackSections
open AffinePullbackComparisonSections

attribute [local irreducible] compositeIso Scheme.Modules.pullback
attribute [local irreducible] AffineTildeSemilinearMap.map moduleSpecΓFunctor specUnit

variable {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ T) (χ : R ⟶ T)
variable (w : Spec.map ψ ≫ Spec.map φ = Spec.map χ)
variable (M : ModuleCat R) (N : ModuleCat S) (P : ModuleCat T)

/-- The bundled original section is the sheaf unit applied to the tilde unit. -/
lemma original_unit_apply (m : M) :
    AffineTildePullbackSectionMap.unit φ M m =
      specUnit φ (tilde M) ((tilde.toTildeΓNatIso (R := R)).hom.app M m) := rfl

attribute [local irreducible] AffineTildePullbackSectionMap.unit

/-- The inverse comparison transports an original coefficient into its iterated pullback. -/
lemma compositeIso_inv_original_unit (m : M) :
    (moduleSpecΓFunctor (R := T)).map
        (compositeIso (Spec.map ψ) (Spec.map φ) (Spec.map χ) w (tilde M)).inv
        (AffineTildePullbackSectionMap.unit χ M m) =
      specUnit ψ ((pullback (Spec.map φ)).obj (tilde M))
        (AffineTildePullbackSectionMap.unit φ M m) := by
  rw [original_unit_apply χ M m, original_unit_apply φ M m]
  exact compositeIso_inv_unit φ ψ χ w (tilde M)
    ((tilde.toTildeΓNatIso (R := R)).hom.app M m)

/-- Pulling back a normalized coefficient map preserves its original section formula. -/
lemma pullback_map_unit (a : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N) (m : M) :
    (moduleSpecΓFunctor (R := T)).map ((pullback (Spec.map ψ)).map (map φ M N a))
        (specUnit ψ ((pullback (Spec.map φ)).obj (tilde M))
          (AffineTildePullbackSectionMap.unit φ M m)) =
      AffineTildePullbackSectionMap.unit ψ N (a m) := by
  rw [specUnit_naturality ψ (map φ M N a),
    AffineTildePullbackSectionMap.semilinearMap_unit φ M N a m]
  exact (original_unit_apply ψ N (a m)).symm

/-- Composable normalized coefficient maps satisfy the full pullback composition law. -/
lemma map_comp
    (a : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N)
    (b : N ⟶ (ModuleCat.restrictScalars ψ.hom).obj P)
    (c : M ⟶ (ModuleCat.restrictScalars χ.hom).obj P)
    (h : ∀ m : M, b (a m) = c m) :
    (compositeIso (Spec.map ψ) (Spec.map φ) (Spec.map χ) w (tilde M)).inv ≫
        (pullback (Spec.map ψ)).map (map φ M N a) ≫ map ψ N P b = map χ M P c := by
  apply AffineTildePullbackSectionMap.hom_ext χ M
  intro m
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  rw [compositeIso_inv_original_unit φ ψ χ w M m,
    pullback_map_unit φ ψ M N a m,
    AffineTildePullbackSectionMap.semilinearMap_unit ψ N P b (a m),
    AffineTildePullbackSectionMap.semilinearMap_unit χ M P c m, h m]

end FLT.Mazur.AffineTildeSemilinearCoherence
