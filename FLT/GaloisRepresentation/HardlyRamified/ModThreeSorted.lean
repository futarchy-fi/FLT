/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CoordinateChange
public import FLT.GaloisRepresentation.HardlyRamified.PureSortedQuotient
public import FLT.GaloisRepresentation.HardlyRamified.ResidualGlobalModel
public import Mathlib.Algebra.Module.Shrink

/-!
# The mod-three quotient conditional on integral sorting

The only additional input is existence of a sorted integral extension for every
category-D object killed by three. Global models, purity, coefficient linearity,
and nontriviality of the constant quotient are proved separately.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ThreeAdicPlan

/-- The integral sorting statement for category-D objects killed by three. -/
def SortedExtensionExists : Prop :=
  ∀ (H : FiniteFlatObject ZInvTwo), InCategoryD H → KilledByQ 3 H →
    Nonempty (SortedFiniteFlatExtension H)

/-- Integral sorting gives the invariant quotient on a small residual representation. -/
theorem modThree_of_sortedExtensionExists_small
    (hsorted : SortedExtensionExists)
    {k : Type*} [Field k] [Finite k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : GaloisRepresentation.IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ π : V →ₗ[k] k, Function.Surjective π ∧
      ∀ (g : Field.absoluteGaloisGroup ℚ) (v : V), π (ρ g v) = π v := by
  obtain ⟨M⟩ := residualPointModule_globalModel hV ρ hρ
  let H := FiniteFlatObject.ofModel M.toModelOverZInvTwo
  let instHModule : Module k H.points := residualPointModuleModule ρ
  let instHFinite : Module.Finite k H.points := residualPointModuleFinite ρ
  let instHComm : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) k H.points :=
    residualPointModuleSMulComm ρ
  have hk : KilledByQ 3 H := residualPointModule_killed ρ _
  obtain ⟨S⟩ := hsorted H M.inCategoryD hk
  exact trivial_quotient_over_coefficients (S.withPureActions hk) hk hV ρ hρ
    (fun _ _ ↦ rfl)

end ThreeAdicPlan

namespace GaloisRepresentation.IsHardlyRamified

/-- A finite three-adic residual representation has an invariant coefficient-linear
quotient, conditional only on the named integral sorting statement. -/
theorem mod_three_of_sortedExtensionExists
    (hsorted : ThreeAdicPlan.SortedExtensionExists)
    {k : Type*} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
      ∀ (g : Field.absoluteGaloisGroup ℚ) (v : V), π (ρ g v) = π v := by
  let instFiniteV : Finite V := Module.finite_of_finite k
  let e : V ≃ₗ[k] Shrink.{0} V :=
    (show Shrink.{0} V ≃ₗ[k] V from Shrink.linearEquiv.{0} k V).symm
  let instFiniteShrink : Module.Finite k (Shrink.{0} V) := Module.Finite.equiv e
  have hd : Module.rank k (Shrink.{0} V) = 2 := by
    rw [Module.rank_eq_ofNat_iff_finrank_eq_ofNat 2, ← e.finrank_eq]
    exact Module.finrank_eq_of_rank_eq hV
  have hr := hρ.conj (show Odd 3 by decide) hV hd e
  obtain ⟨π, hπ, hinv⟩ := ThreeAdicPlan.modThree_of_sortedExtensionExists_small hsorted hd hr
  refine ⟨π.comp e.toLinearMap, hπ.comp e.surjective, ?_⟩
  intro g v
  have h := hinv g (e v)
  simpa [GaloisRep.conj_apply_apply] using h

end GaloisRepresentation.IsHardlyRamified
