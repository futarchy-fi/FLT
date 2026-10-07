/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIteratedPullbackSections

/-!
# Global sections of the geometric pullback comparison

The forward and inverse comparisons preserve the actual adjunction units.
Bundled section formulas keep later coherence proofs independent of the
implementation of affine global sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffinePullbackComparisonSections
open AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An isomorphism carries a specified image back to its original section. -/
lemma inverse_section {R : CommRingCat.{u}} {M N : ModuleCat R}
    (e : M ≅ N) (x : M) (y : N) (h : e.hom x = y) : e.inv y = x := by
  rw [← h, ← ConcreteCategory.comp_apply, e.hom_inv_id, ConcreteCategory.id_apply]

attribute [local irreducible] compositeIso Scheme.Modules.pullback


variable {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ T) (χ : R ⟶ T)
variable (w : Spec.map ψ ≫ Spec.map φ = Spec.map χ)

attribute [local irreducible] moduleSpecΓFunctor specUnit

/-- On global sections the forward comparison preserves the iterated units. -/
lemma compositeIso_specUnit (Q : (Spec R).Modules) (m : moduleSpecΓFunctor.obj Q) :
    (moduleSpecΓFunctor (R := T)).map
        (compositeIso (Spec.map ψ) (Spec.map φ) (Spec.map χ) w Q).hom
        (specUnit ψ ((pullback (Spec.map φ)).obj Q) (specUnit φ Q m)) =
      specUnit χ Q m := by
  rw [spec_map_apply, specUnit_apply, specUnit_apply, specUnit_apply]
  unfold moduleSpecΓFunctor at m ⊢
  exact compositeIso_unit (Spec.map ψ) (Spec.map φ) (Spec.map χ) w Q m

/-- The inverse comparison sends the direct unit to the two iterated units. -/
lemma compositeIso_inv_unit (Q : (Spec R).Modules) (m : moduleSpecΓFunctor.obj Q) :
    (moduleSpecΓFunctor (R := T)).map
        (compositeIso (Spec.map ψ) (Spec.map φ) (Spec.map χ) w Q).inv
        (specUnit χ Q m) =
      specUnit ψ ((pullback (Spec.map φ)).obj Q) (specUnit φ Q m) := by
  exact inverse_section ((moduleSpecΓFunctor (R := T)).mapIso
    (compositeIso (Spec.map ψ) (Spec.map φ) (Spec.map χ) w Q)) _ _
      (compositeIso_specUnit φ ψ χ w Q m)
end FLT.Mazur.AffinePullbackComparisonSections
