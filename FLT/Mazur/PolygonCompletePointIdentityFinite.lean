/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginCartesian
public import FLT.Mazur.CartesianIdentityFiniteNeighborhood
public import FLT.Mazur.CartesianIdentityFactorization

/-!
# A finite neighborhood of the original complete-base identity

Normalize the actual Cartesian origin square by the original affine-base
isomorphism. The cubic morphism is finite near the whole original identity,
including the closed fiber, and retains the full scheme-valued identity tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "s" => completeBaseMarking K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i

/-- The actual origin square expressed over the unchanged complete coefficient scheme. -/
theorem completePointIdentity_isPullback : IsPullback (𝟙 S₀) (s) ((s) ≫ (g)) (g) := by
  apply (completePointToIntegralCubic_origin_isPullback K n h i).flip.of_iso
    (Iso.refl _) (asIso (S₀).toSpecΓ).symm (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv,
      completePointToIntegralCubic_marking, IsIso.inv_hom_id_assoc]
  · simp

/-- Every scheme-valued test over the original cubic identity factors through the marking. -/
theorem completePointIdentity_factorization {T : Scheme} (t : T ⟶ S₀)
    (a : T ⟶ exactVeroneseProj K n h)
    (ha : t ≫ (S₀).toSpecΓ ≫ integralCurveZero (W) = a ≫ (g)) : t ≫ (s) = a := by
  apply CartesianIdentity.factorization (s) (g) (completePointIdentity_isPullback K n h i)
  rwa [completePointToIntegralCubic_marking]

/-- The entire fiber over any original identity point is its original marking point. -/
theorem completePointIdentity_preimage_singleton (t : S₀) :
    (g) ⁻¹' {(g) ((s) t)} = {(s) t} :=
  CartesianIdentity.preimage_singleton (s) (g) (completePointIdentity_isPullback K n h i) t

/-- One open around the whole identity image makes the original cubic morphism finite. -/
theorem completePointIdentity_finite_neighborhood :
    ∃ U : (integralCurve (W)).Opens,
      Set.range ((s) ≫ (g)) ⊆ U ∧ IsFinite ((g) ∣_ U) := by
  let _ := completePointToIntegralCubic_proper K n h i
  exact CartesianIdentity.exists_finite_identity_neighborhood (s) (g)
    (completePointIdentity_isPullback K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
