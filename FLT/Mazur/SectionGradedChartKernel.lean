/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedPowerRatios
public import FLT.Mazur.SectionCoverCoordinates

/-!
# Killing homogeneous chart kernels by a denominator power

On a finite affine generator cover, a section vanishing on one generator
open is annihilated globally by a power of that generator in the actual
section ring. The proof uses affine scalar localization and works over
nonreduced rings, without assuming that restriction is injective.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.SectionGradedChartKernel
open FCurve ModuleLineBundleTensorPullback SectionCover
open SectionGradedSum SectionGradedMultiplication SectionGradedPowerRatios
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]
  {ι : Type v}

/-- A homogeneous numerator vanishing on a chart is killed by a power of its generator. -/
theorem exists_pow_mul_eq_zero [Finite ι] (d : ℕ)
    (s : ι → Γ(tensorPower L d, ⊤)) (haff : ∀ j, IsAffineOpen (chart s j))
    (hcover : ⨆ j, chart s j = ⊤) (i : ι) (n : ℕ)
    (t : Γ(tensorPower L (d * n), ⊤))
    (ht : (tensorPower L (d * n)).presheaf.map (homOfLE le_top : chart s i ⟶ ⊤).op t = 0) :
    ∃ m : ℕ, (of L ⊤ d (s i)) ^ m * of L ⊤ (d * n) t = 0 := by
  let b (j : ι) : Γ(X, chart s j) := coefficient L hL.out d (s j) n _ le_rfl t
  have hb (j : ι) : res (inf_le_left : chart s j ⊓ chart s i ≤ _) (b j) = 0 := by
    rw [show res (inf_le_left : chart s j ⊓ chart s i ≤ _) (b j) =
      coefficient L hL.out d (s j) n _ inf_le_left t from
        coefficient_restrict L hL.out d (s j) n inf_le_left le_rfl t]
    apply coefficient_eq_zero
    have ht' := congrArg ((tensorPower L (d * n)).presheaf.map
      (homOfLE (inf_le_right : chart s j ⊓ chart s i ≤ chart s i)).op) ht
    simp only [map_zero, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] at ht'
    exact ht'
  obtain ⟨m, hm⟩ := AffineOpenDenominators.finite_kernels
    (chart s) (fun j ↦ chart s j ⊓ chart s i) haff
    (fun j ↦ ratio s j i (chart s j) le_rfl) b
    (fun j ↦ inf_eq_basicOpen s j i _ le_rfl) hb
  refine ⟨m, SectionGradedRestriction.eq_zero_of_cover L (chart s) hcover
    (mul_mem_grade L ⊤ (SetLike.pow_mem_graded m (show of L ⊤ d (s i) ∈ grade L ⊤ d
      from ⟨s i, rfl⟩)) (show of L ⊤ (d * n) t ∈ grade L ⊤ (d * n) from ⟨t, rfl⟩)) ?_⟩
  intro j
  let ρ := restrictRingHom L (chart s j) (homOfLE le_top)
  have hs : ρ (of L ⊤ d (s i)) = ratio s j i (chart s j) le_rfl •
      ρ (of L ⊤ d (s j)) := by
    dsimp only [ρ]
    rw [show restrictRingHom L (chart s j) (homOfLE le_top) (of L ⊤ d (s i)) =
      of L (chart s j) d ((tensorPower L d).presheaf.map
        (homOfLE (show chart s j ≤ ⊤ from le_top)).op (s i)) from restrict_of L _ _ _]
    have he := sectionRatioOn_smul (tensorPower L d) (s j) (chart s j) le_rfl (s i)
    rw [← he, _root_.map_smul]
    exact congrArg (fun z ↦ ratio s j i (chart s j) le_rfl • z)
      (restrict_of L _ d (s j)).symm
  have htj : ρ (of L ⊤ (d * n) t) = b j • (ρ (of L ⊤ d (s j))) ^ n :=
    (coefficient_smul L hL.out d (s j) n _ le_rfl t).symm
  change ρ (_ ^ m * _) = 0
  rw [map_mul, map_pow, hs, htj, smul_pow, _root_.smul_mul_smul, hm j, zero_smul]

end FLT.Mazur.SectionGradedChartKernel
