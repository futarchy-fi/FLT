/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientCartesian
public import FLT.Mazur.WeierstrassSmoothFaithfulCoefficientDescent

/-!
# Faithfully flat detection of the actual finite-model action

The concrete coefficient action domain covers the entire original action domain.
Consequently equality with the genuine finite-model action descends from a
faithfully flat coefficient extension, without a split-node hypothesis.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (S : Type u) [CommRing S] [Algebra R S]
  (hS : (algebraMap R S).FaithfullyFlat)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "p" => pullback.snd q base
local notation "c" => finiteGlobalCoefficientActionProduct hπ data j hj S

include hS in
/-- The actual coefficient projection of the whole finite model is faithfully flat. -/
theorem finiteGlobalTensorProjection_flat_surjective : Flat p ∧ Surjective p := by
  obtain ⟨hq, hq'⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap R S))).mpr hS
  let _ := hq
  let _ := hq'
  exact ⟨inferInstance, inferInstance⟩

include hS in
/-- The genuine extended action domain faithfully covers its entire original domain. -/
theorem finiteGlobalCoefficientActionProduct_flat_surjective : Flat c ∧ Surjective c := by
  obtain ⟨hf, hs⟩ := finiteGlobalTensorProjection_flat_surjective hπ data j hj S hS
  exact ⟨MorphismProperty.of_isPullback
    (finiteGlobalCoefficientActionProduct_isPullback hπ data j hj S).flip hf,
    MorphismProperty.of_isPullback
      (finiteGlobalCoefficientActionProduct_isPullback hπ data j hj S).flip hs⟩

include hS in
/-- The actual coefficient action domain detects every original scheme morphism. -/
theorem finiteGlobalCoefficientActionProduct_epi : Epi c := by
  obtain ⟨hf, hs⟩ := finiteGlobalCoefficientActionProduct_flat_surjective hπ data j hj S hS
  let _ := hf
  let _ := hs
  exact Flat.epi_of_flat_of_surjective _

include hS in
/-- Equality on the concrete extended action domain descends to the whole original domain. -/
theorem finiteGlobalActionProduct_hom_ext {Y : Scheme.{u}}
    (a b : finiteGlobalActionProduct hπ data j hj ⟶ Y) (h : c ≫ a = c ≫ b) : a = b := by
  let _ := finiteGlobalCoefficientActionProduct_epi hπ data j hj S hS
  exact (cancel_epi c).mp h

include hS in
/-- An action comparison after a splitting cover determines the actual original action. -/
theorem finiteGlobalAction_eq_of_coefficient
    (a : finiteGlobalActionProduct hπ data j hj ⟶ finiteGlobalModel hπ data j hj)
    (h : c ≫ a = finiteGlobalCoefficientAction hπ data j hj S ≫ p) :
    a = finiteGlobalAction hπ data j hj := by
  apply finiteGlobalActionProduct_hom_ext hπ data j hj S hS
  exact h.trans (finiteGlobalCoefficientAction_projection hπ data j hj S)

end FLT.Mazur.WeierstrassDividedDepth
