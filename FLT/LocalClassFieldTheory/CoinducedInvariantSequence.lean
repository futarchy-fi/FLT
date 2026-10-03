/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedSubgroupShift
public import FLT.LocalClassFieldTheory.SubgroupNormDecomposition

/-!
# The invariant coefficient sequence

Vanishing of subgroup Tate H⁰ of the shifted coefficients makes the
invariant projection surjective: lift a norm preimage, then take its norm.
This constructs the first half of the quotient two-extension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (M : Rep.{0} k G)
  (N : Subgroup G) [N.Normal]

local notation "I" => coinducedCoefficients M
local notation "Q" => shiftedCoefficients M
local notation "J" => Rep.quotientToInvariantsFunctor k N
local notation "i" => CategoryTheory.Functor.map J (coinducedInclusion M)
local notation "π" => CategoryTheory.Functor.map J (shiftedProjection M)

/-- The invariant coefficient maps form a short complex for the quotient group. -/
def coinducedInvariantSequence : ShortComplex (Rep k (G ⧸ N)) :=
  ShortComplex.mk i π (by
    ext x
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x.val, rfl⟩)

/-- Injectivity of the orbit inclusion also gives exactness on subgroup invariants. -/
theorem coinducedInvariantSequence_kernel
    (x : Rep.quotientToInvariants I N) (hx : (π).hom x = 0) :
    ∃ y : Rep.quotientToInvariants M N, (i).hom y = x := by
  have hx' : (shiftedProjection M).hom x.val = 0 := congrArg Subtype.val hx
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx'
  refine ⟨⟨y, fun n => ?_⟩, Subtype.ext hy⟩
  apply coinducedInclusion_injective M
  exact (Rep.hom_comm_apply (coinducedInclusion M) (n : G) y).trans
    ((congrArg ((I).ρ (n : G)) hy).trans ((x.property n).trans hy.symm))

/-- Inflation of invariant coefficients maps to the original coefficient sequence. -/
def coinducedInvariantSequenceMap :
    (coinducedInvariantSequence M N).map (Rep.resFunctor (QuotientGroup.mk' N)) ⟶
      coinducedCoefficientSequence M where
  τ₁ := Rep.ofHom (M.ρ.quotientToInvariants_lift N)
  τ₂ := Rep.ofHom ((I).ρ.quotientToInvariants_lift N)
  τ₃ := Rep.ofHom ((Q).ρ.quotientToInvariants_lift N)
  comm₁₂ := by ext x; rfl
  comm₂₃ := by ext x; rfl

variable [Fintype N]

/-- The invariant projection is surjective when the shifted norm quotient vanishes. -/
theorem coinducedInvariantProjection_surjective
    (h₀ : Limits.IsZero (tateCohomology (Rep.res N.subtype Q) 0)) :
    Function.Surjective (π).hom := by
  intro x
  have hx : d₀₁ (Rep.res N.subtype Q) x.val = 0 := by
    ext n
    exact sub_eq_zero.mpr (x.property n)
  obtain ⟨y, hy⟩ := norm_surjective_of_tate_zero (Rep.res N.subtype Q) h₀ x.val hx
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective
    (LinearMap.range (coinducedInclusion M).hom.toLinearMap) y
  refine ⟨subgroupNormInvariant I N z, ?_⟩
  apply Subtype.ext
  change (shiftedProjection M).hom ((Rep.res N.subtype I).norm.hom z) = x.val
  have hn := congrArg (fun f => f.hom z)
    (Rep.norm_comm ((Rep.resFunctor N.subtype).map (shiftedProjection M)))
  change (Rep.res N.subtype Q).norm.hom ((shiftedProjection M).hom z) =
    (shiftedProjection M).hom ((Rep.res N.subtype I).norm.hom z) at hn
  change (shiftedProjection M).hom z = y at hz
  exact hn.symm.trans ((congrArg (Rep.res N.subtype Q).norm.hom hz).trans hy)

/-- Both invariant coefficient maps are exact, including the final surjection. -/
theorem coinducedInvariantSequence_shortExact
    (h₀ : Limits.IsZero (tateCohomology (Rep.res N.subtype Q) 0)) :
    (coinducedInvariantSequence M N).ShortExact where
  mono_f := (Rep.mono_iff_injective _).mpr (by
    intro x y h
    apply Subtype.ext
    exact coinducedInclusion_injective M (congrArg Subtype.val h))
  epi_g := (Rep.epi_iff_surjective _).mpr (coinducedInvariantProjection_surjective M N h₀)
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k (G ⧸ N)) (ModuleCat k))]
    exact (ShortComplex.moduleCat_exact_iff _).mpr (coinducedInvariantSequence_kernel M N)

end LocalClassFieldTheory
