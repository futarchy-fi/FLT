/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FiniteUniformizerRootCharacter
public import FLT.AbsoluteGaloisGroup.TameRootIntegralModel
public import FLT.AbsoluteGaloisGroup.UniformizerCharacterPowers
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.TotalRamification

/-!
# Ramification exponents in an arbitrary finite model containing the tame root

If a finite Galois field contains the chosen tame root, its valuation k
satisfies e = (q - 1) k. The k-th power of its uniformizer character is the
specified absolute tame character after the actual residue inclusion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing IsDiscreteValuationRing
namespace LocalRamification
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "F" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure F
variable (N : OpenNormalSubgroup (Field.absoluteGaloisGroup (v.adicCompletion K)))
local notation "L" => IntermediateField.fixedField N.toSubgroup
local notation "D" => IntegralClosure O L
local notation "n" => Nat.card (ResidueField O) - 1
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

set_option maxHeartbeats 1000000 in
-- Integral-closure actions and finite inertia restrictions require larger elaboration budgets.
set_option synthInstance.maxHeartbeats 100000 in
/-- The root's valuation is the ramification exponent relating finite and absolute characters. -/
theorem finiteTameRoot_character_exponent {y : D}
    (hy : (y.1 : Ω) = tameUniformizerRoot v) {π : D} (hπ : Irreducible π) :
    ∃ k : ℕ, (IsLocalRing.maximalIdeal D).ramificationIdx O = n * k ∧
      ∀ σ : localInertiaGroup v,
        ResidueField.map (finiteClosureToAbsolute v N)
          ((ThreeAdicPlan.uniformizerCharacter hπ (finiteIdealInertiaRestriction v N σ) :
            ResidueField D) ^ k) = residueFieldMap v (tameCharacter v σ : ResidueField O) := by
  let : Module.Finite O D := IsIntegralClosure.finite O F L (integralClosure O L)
  let : FaithfulSMul O D := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply Subtype.ext
    apply (algebraMap F L).injective
    exact congrArg Subtype.val h
  have hy0 : y ≠ 0 := by
    intro h
    apply tameUniformizerRoot_ne_zero v
    rw [← hy, h]
    rfl
  have hroot : y ^ n = algebraMap O D (tameUniformizer v) := by
    apply Subtype.ext
    apply Subtype.ext
    change (y.1 : Ω) ^ n = algebraMap F Ω (tameUniformizer v).1
    rw [hy]
    exact tameUniformizerRoot_spec v
  obtain ⟨k, hk, hratio⟩ := ThreeAdicPlan.exists_uniformizer_power_ratio (G := Gal(L/F)) hπ hy0
  refine ⟨k, ?_, fun σ ↦ ?_⟩
  · have hv := congrArg (addVal D) hroot
    rw [addVal_pow, hk, nsmul_eq_mul,
      addValMapUniformizerEqRamificationIdx (tameUniformizer_irreducible v)] at hv
    exact_mod_cast hv.symm
  · obtain ⟨z, hz, hres⟩ := hratio (finiteIdealInertiaRestriction v N σ)
    let i := finiteClosureToAbsolute v N
    have he : i z = LocalRoot.integralRatio v (tameDegree_pos v)
        (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
          (tameUniformizer_spec v) (Subtype.ext h)) (tameUniformizerRoot_spec v) σ := by
      apply Subtype.ext
      change (i z).1 = σ.val (tameUniformizerRoot v) / tameUniformizerRoot v
      apply (eq_div_iff (tameUniformizerRoot_ne_zero v)).mpr
      have hh := congrArg (fun x : D ↦ (i x).1) hz
      change ((σ.val.restrictNormal L) y.1 : Ω) = (i z).1 * (y.1 : Ω) at hh
      rw [AlgEquiv.restrictNormal_apply, hy] at hh
      exact hh.symm
    rw [← hres]
    change residue (IntegralClosure O Ω) (i z) = _
    rw [he]
    exact (tameCharacter_residue_eq_rootCharacter v (tameUniformizer_spec v)
      (tameUniformizerRoot_spec v) σ).symm

end LocalRamification
