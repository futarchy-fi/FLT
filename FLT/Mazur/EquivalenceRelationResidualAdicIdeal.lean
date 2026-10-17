/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationResidualPermutationOpen
public import FLT.Mazur.EquivalenceRelationCompleteThickenings
public import FLT.Mazur.PolygonDivisorPowerPullback

/-!
# Complete adic stages have empty pullback to the actual residual branches

The complete-support ideal becomes the unit ideal on the residual open.
Consequently every positive complete thickening misses that open. This records
precisely why compatibility at all complete adic orders places no condition
on these remaining original branches.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SourceRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  {S : Scheme.{0}} (j : S ⟶ source p q I o) [Mono j] [S.IsSeparated]
  (ρ : Equiv.Perm I →* Aut S)
  (hj : ∀ σ, (ρ σ).hom ≫ j = j ≫ (action e I o σ).hom)
local notation "r" => SourceRestriction.fst j j
local notation "O" => residualPermutationOpen e I o j ρ hj
set_option quotPrecheck false
local notation "b" => (O).ι ≫ (r) ≫ j

/-- The original complete-support ideal is the unit ideal on every residual branch. -/
theorem residual_completeSupportIdeal_eq_top :
    (completeSupportIdeal (p := p) (q := q) I o).comap b = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  apply TopologicalSpace.Closeds.ext
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact residualPermutationOpen_first_incomplete e I o j ρ hj x hx

/-- Every complete ideal power is likewise the unit ideal on the same residual open. -/
theorem residual_completeSupportIdeal_pow_eq_top (n : ℕ) :
    (completeSupportIdeal (p := p) (q := q) I o ^ n).comap b = ⊤ := by
  rw [FCurve.idealSheaf_comap_pow, residual_completeSupportIdeal_eq_top]
  exact one_pow n

/-- The original complete thickening at each order has empty residual pullback. -/
theorem residual_completeStage_isEmpty (n : ℕ) :
    IsEmpty (pullback b (completeThickeningInclusion I o n) : Scheme) := by
  constructor
  intro x
  have hc : completeThickeningInclusion I o n
      (pullback.snd b (completeThickeningInclusion I o n) x) ∈
        completePointLocus (p := p) (q := q) I o :=
    (completeThickeningInclusion_range I o n).le ⟨_, rfl⟩
  have he := congrArg (fun f ↦ f x)
    (pullback.condition (f := b) (g := completeThickeningInclusion I o n))
  exact residualPermutationOpen_first_incomplete e I o j ρ hj
    (pullback.fst b (completeThickeningInclusion I o n) x) (he.symm ▸ hc)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
