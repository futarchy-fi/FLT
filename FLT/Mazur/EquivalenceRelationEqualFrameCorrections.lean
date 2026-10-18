/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationEqualFrameOverlap
public import FLT.Mazur.FiniteGroupBoundaryChartRestriction

/-!
# Construct embedding corrections inside a common stable affine frame chart

Freeness supplies one invariant boundary lift on the common affine chart.
Restricting that single lift solves every embedding equation between arbitrary
stable subopens. Subtraction constructs one simultaneous family of exact
boundary-zero corrections. The residual equations are not asserted to vanish.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient FiniteGroupOpenRelation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (Z : (source p q I o).Opens)
  (hZ : ∀ σ : Equiv.Perm I, (action e I o σ).hom ⁻¹ᵁ Z = Z)
local notation "N" => source p q I o
local notation "τ" => action e I o

/-- Restrictions of one invariant coefficient solve all same-frame graph equations. -/
theorem mixedEqualFrame_restrictions_equalize
    (U V : (source p q I o).Opens)
    (hU : ∀ σ, (τ σ).hom ⁻¹ᵁ U = U) (hV : ∀ σ, (τ σ).hom ⁻¹ᵁ V = V)
    (hUZ : U ≤ Z) (hVZ : V ≤ Z)
    (w : invariantCoordinates (restrictedAction τ Z hZ)) (ι : I ↪ I) :
    ((mixedEmbeddingTestOpen e o o (mixedChartOpen o o U V).ι ι).ι ≫
      mixedChartFirst o o U V).appTop
        (invariantRestriction τ Z hZ U hU hUZ w).val =
    ((mixedEmbeddingTestOpen e o o (mixedChartOpen o o U V).ι ι).ι ≫
      mixedChartSecond o o U V).appTop
        (invariantRestriction τ Z hZ V hV hVZ w).val := by
  apply (mixedEqualFrameBranch_equation_iff e I o U V hV ι _ _).mpr
  simp only [invariantRestriction_val]
  change (((N).homOfLE inf_le_left ≫ (N).homOfLE hUZ).appTop w.val) =
    (((N).homOfLE inf_le_right ≫ (N).homOfLE hVZ).appTop w.val)
  rw [Scheme.homOfLE_homOfLE, Scheme.homOfLE_homOfLE]

variable {B : Scheme.{0}} (i : B ⟶ source p q I o) [IsClosedImmersion i]
  (ρ : Equiv.Perm I →* Aut B)
  (hi : ∀ σ, (ρ σ).hom ≫ i = i ≫ (action e I o σ).hom)
local notation "β" => boundaryOpenAction ρ τ i hi Z hZ
local notation "bZ" => invariantMap β (restrictedAction τ Z hZ) (i ∣_ Z)
  (boundaryOpen_equivariant ρ τ i hi Z hZ)

include hi in
/-- One common affine lift constructs simultaneous exact corrections on every stable subchart. -/
theorem exists_equalFrame_embedding_corrections (ha : IsAffineOpen Z)
    {T : Type} (U : T → (source p q I o).Opens)
    (hU : ∀ a σ, (τ σ).hom ⁻¹ᵁ U a = U a) (hUZ : ∀ a, U a ≤ Z)
    (t : invariantCoordinates β)
    (u : ∀ a, invariantCoordinates (restrictedAction τ (U a) (hU a)))
    (hu : ∀ a, invariantMap (boundaryOpenAction ρ τ i hi (U a) (hU a))
      (restrictedAction τ (U a) (hU a)) (i ∣_ U a)
      (boundaryOpen_equivariant ρ τ i hi (U a) (hU a)) (u a) =
      boundaryInvariantRestriction ρ τ i hi Z hZ (U a) (hU a) (hUZ a) t) :
    ∃ z : ∀ a, invariantCoordinates (restrictedAction τ (U a) (hU a)),
      (∀ a, (i ∣_ U a).appTop (z a).val = 0) ∧
      ∀ a b (ι : I ↪ I),
        ((mixedEmbeddingTestOpen e o o (mixedChartOpen o o (U a) (U b)).ι ι).ι ≫
          mixedChartFirst o o (U a) (U b)).appTop (z a).val -
        ((mixedEmbeddingTestOpen e o o (mixedChartOpen o o (U a) (U b)).ι ι).ι ≫
          mixedChartSecond o o (U a) (U b)).appTop (z b).val =
        ((mixedEmbeddingTestOpen e o o (mixedChartOpen o o (U a) (U b)).ι ι).ι ≫
          mixedChartFirst o o (U a) (U b)).appTop (u a).val -
        ((mixedEmbeddingTestOpen e o o (mixedChartOpen o o (U a) (U b)).ι ι).ι ≫
          mixedChartSecond o o (U a) (U b)).appTop (u b).val := by
  obtain ⟨w, hw⟩ := boundaryOpen_invariantMap_surjective ρ τ i hi Z hZ
    (fun _ _ a σ h ↦ action_free e I o a σ h) ha t
  let v a := invariantRestriction τ Z hZ (U a) (hU a) (hUZ a) w
  refine ⟨fun a ↦ u a - v a, ?_, ?_⟩
  · intro a
    have hv := boundary_chart_lift_restriction ρ τ i hi Z hZ (U a) (hU a)
      (hUZ a) w t hw
    have hb := congrArg Subtype.val ((hu a).trans hv.symm)
    change (i ∣_ U a).appTop ((u a).val - (v a).val) = 0
    rw [map_sub, sub_eq_zero]
    exact hb
  · intro a b ι
    have hv := mixedEqualFrame_restrictions_equalize e I o Z hZ (U a) (U b)
      (hU a) (hU b) (hUZ a) (hUZ b) w ι
    have hsub (a : T) : (u a - v a).val = (u a).val - (v a).val := rfl
    rw [hsub, hsub, map_sub, map_sub]
    dsimp only [v]
    rw [hv]
    abel

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
