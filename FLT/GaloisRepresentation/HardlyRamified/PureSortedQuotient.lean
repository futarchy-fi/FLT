/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.GaloisRepresentation.HardlyRamified.ResidualCharacteristic
public import FLT.GaloisRepresentation.HardlyRamified.RationalComplexConjugation
public import FLT.GroupScheme.SortedFiltrationCoefficientQuotient
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Invariant functionals from sorted finite-flat filtrations

The integral sorted extension carries full pointwise actions on its two pieces.
Its coefficient quotient is nonzero by the cyclotomic determinant in dimension two.
A linear functional on that quotient gives the invariant coefficient-linear quotient.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- A sorted integral extension together with the full actions on both pieces. -/
structure SortedFiltrationWithPureActions (H : FiniteFlatObject ZInvTwo)
    extends SortedFiniteFlatExtension H where
  /-- The multiplicative part has the cyclotomic point action modulo three. -/
  leftAction : ∀ (σ : Γ) (x : left.points), σ • x =
    (((cyclotomicCharacter (AlgebraicClosure ℚ) 3 σ.toRingEquiv).val.toZModPow 1).val) • x
  /-- The constant part has trivial point action. -/
  rightAction : ∀ (σ : Γ) (x : right.points), σ • x = x

/-- The purity theorems supply the full actions for a sorted object killed by three. -/
def SortedFiniteFlatExtension.withPureActions {H : FiniteFlatObject ZInvTwo}
    (S : SortedFiniteFlatExtension H) (hkill : KilledByQ 3 H) :
    SortedFiltrationWithPureActions H where
  toSortedFiniteFlatExtension := S
  leftAction := S.left.points.cyclotomic_nsmul_of_characterDual_trivial 3 1
    (fun x ↦ by simpa using S.extension.killedByLeft hkill x)
    (pure_one_characterDual_of_muThree_filtration S.left S.leftFiltration)
  rightAction σ x := by
    simpa using pure_one_of_constantThree_filtration S.right S.rightFiltration σ x

variable {H : FiniteFlatObject ZInvTwo} (S : SortedFiltrationWithPureActions H)
    (hkill : KilledByQ 3 H) {k : Type*} [Field k] [Module k H.points]
    [SMulCommClass Γ k H.points]

/-- A proper multiplicative coefficient submodule gives a surjective invariant functional. -/
theorem SortedFiltrationWithPureActions.invariantFunctional_of_ne_top
    (hne : S.toSortedFiniteFlatExtension.pointSubmodule hkill k ≠ ⊤) :
    ∃ π : H.points →ₗ[k] k, Function.Surjective π ∧
      ∀ (σ : Γ) (x : H.points), π (σ • x) = π x := by
  let Q := H.points ⧸ S.toSortedFiniteFlatExtension.pointSubmodule hkill k
  let instNontrivialQ : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨x, hx⟩ := exists_ne (0 : Q)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hx
  let q := S.toSortedFiniteFlatExtension.coefficientProjection hkill k
  refine ⟨f.comp q, ?_, ?_⟩
  · apply Function.Surjective.comp _
      (S.toSortedFiniteFlatExtension.coefficientProjection_surjective hkill k)
    intro a
    exact ⟨a • x, by simp [hf]⟩
  · intro σ x
    exact congrArg f
      (S.toSortedFiniteFlatExtension.coefficientProjection_invariant hkill k σ x)

/-- A rank-two cyclotomic determinant prevents the multiplicative part from being everything. -/
theorem SortedFiltrationWithPureActions.pointSubmodule_ne_top
    [Finite k] [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    [Module.Finite k H.points] (hV : Module.rank k H.points = 2)
    (ρ : GaloisRep ℚ k H.points)
    (hρ : GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (haction : ∀ (σ : Γ) (x : H.points), ρ σ x = σ • x) :
    S.toSortedFiniteFlatExtension.pointSubmodule hkill k ≠ ⊤ := by
  let instCharThree : CharP k 3 := charP_three_of_finite_padic_algebra k
  intro htop
  have hscalar : ρ rationalComplexConjugation = (2 : k) • (1 : Module.End k H.points) := by
    ext x
    have hx : x ∈ S.toSortedFiniteFlatExtension.pointSubmodule hkill k := by
      rw [htop]
      trivial
    obtain ⟨y, rfl⟩ := hx
    change ρ rationalComplexConjugation (FiniteFlatObject.pointMap S.extension.inclusion y) = _
    rw [haction, ← map_smul]
    have hy := S.leftAction rationalComplexConjugation y
    rw [rationalComplexConjugation_cyclotomic] at hy
    norm_num only [map_neg, map_one, pow_one, ZMod.val_neg_one] at hy
    rw [hy, map_nsmul]
    change (2 : ℕ) • (FiniteFlatObject.pointMap S.extension.inclusion y) =
      (2 : k) • (FiniteFlatObject.pointMap S.extension.inclusion y)
    simp only [two_smul]
  have hd := hρ.det rationalComplexConjugation
  change LinearMap.det (ρ rationalComplexConjugation) = _ at hd
  rw [hscalar, LinearMap.det_smul, map_one,
    Module.finrank_eq_of_rank_eq hV, rationalComplexConjugation_cyclotomic, map_neg, map_one] at hd
  have hc : (3 : k) = 0 := CharP.cast_eq_zero k 3
  have hone : (1 : k) = 0 := by linear_combination 2 * hc - hd
  exact one_ne_zero hone

include S hkill in
/-- The sorted pure filtration supplies a surjective invariant functional over the
original coefficient field, including nonprime finite coefficient fields. -/
theorem trivial_quotient_over_coefficients
    [Finite k] [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    [Module.Finite k H.points] (hV : Module.rank k H.points = 2)
    (ρ : GaloisRep ℚ k H.points)
    (hρ : GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (haction : ∀ (σ : Γ) (x : H.points), ρ σ x = σ • x) :
    ∃ π : H.points →ₗ[k] k, Function.Surjective π ∧
      ∀ (σ : Γ) (x : H.points), π (ρ σ x) = π x := by
  obtain ⟨π, hπ, hinv⟩ := SortedFiltrationWithPureActions.invariantFunctional_of_ne_top S hkill
    (SortedFiltrationWithPureActions.pointSubmodule_ne_top S hkill hV ρ hρ haction)
  exact ⟨π, hπ, fun σ x ↦ by rw [haction]; exact hinv σ x⟩

end ThreeAdicPlan
