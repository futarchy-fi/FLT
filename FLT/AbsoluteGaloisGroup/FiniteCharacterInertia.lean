/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FirstRamificationRestriction
public import FLT.AbsoluteGaloisGroup.OpenNormalFixedField
public import FLT.GaloisRepresentation.Extensions.FiniteCoefficientWildKernel

/-!
# Absolute characters on their actual finite inertia model

The open kernel of a continuous finite coefficient character constructs a
finite Galois field. Absolute inertia surjects onto the inertia of its integral
closure, and the character kills the pulled-back uniformizer kernel there.
This does not identify that character with a specified niveau-one character.
-/

@[expose] public noncomputable section
open NumberField IsLocalRing GaloisRepresentation.Extensions
namespace LocalRamification
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Γ" => Field.absoluteGaloisGroup Kv

attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR
  finiteLevel_residue_finite

/-- The actual restriction from absolute inertia into finite ideal inertia. -/
def finiteIdealInertiaRestriction (N : OpenNormalSubgroup Γ) :
    localInertiaGroup v →*
      (maximalIdeal (IntegralClosure O (IntermediateField.fixedField N.toSubgroup))).inertia
        Gal(IntermediateField.fixedField N.toSubgroup/Kv) :=
  ((AlgEquiv.restrictNormalHom (IntermediateField.fixedField N.toSubgroup)).domRestrict
    (localInertiaGroup v)).codRestrict _ (by
      intro g
      rw [← map_localInertiaGroup_eq_finiteInertia v N]
      exact ⟨g.val, g.property, rfl⟩)

/-- Every automorphism of the finite ideal inertia lifts to absolute inertia. -/
theorem finiteIdealInertiaRestriction_surjective (N : OpenNormalSubgroup Γ) :
    Function.Surjective (finiteIdealInertiaRestriction v N) := by
  intro g
  have hg := g.property
  simp only [← map_localInertiaGroup_eq_finiteInertia v N] at hg
  obtain ⟨a, ha, he⟩ := hg
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

variable {k : Type*} [Field k] [TopologicalSpace k] [DiscreteTopology k]
  (χ : Field.absoluteGaloisGroup (v.adicCompletion K) →* kˣ) (hc : Continuous χ)

/-- The actual open normal kernel of the specified character. -/
def characterOpenNormal : OpenNormalSubgroup Γ where
  toSubgroup := χ.ker
  isOpen' := hc.isOpen_preimage _ (isOpen_discrete {1})

/-- The finite Galois character obtained from this kernel's fixed field. -/
def finiteModelCharacter : Gal(openNormalFixedField (characterOpenNormal v χ hc)/Kv) →* kˣ :=
  (QuotientGroup.kerLift χ).comp
    (openNormalQuotientEquiv (characterOpenNormal v χ hc)).symm.toMonoidHom

/-- Restriction to the constructed finite field recovers the given absolute character. -/
theorem finiteModelCharacter_restrict (g : Γ) :
    finiteModelCharacter v χ hc
      (AlgEquiv.restrictNormalHom (openNormalFixedField (characterOpenNormal v χ hc)) g) =
        χ g := by
  change QuotientGroup.kerLift χ
    ((openNormalQuotientEquiv (characterOpenNormal v χ hc)).symm _) = χ g
  rw [← openNormalQuotientEquiv_mk, MulEquiv.symm_apply_apply]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Integral-closure action instances need a larger typeclass-search budget.
set_option maxHeartbeats 1000000 in
-- Integral closures and their finite Galois actions require additional elaboration time.
/-- On its actual finite DVR model, an absolute finite coefficient character
kills the uniformizer kernel pulled back along the surjective inertia restriction. -/
theorem finiteModelCharacter_uniformizer_kernel [Finite k]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p] [CharP k p]
    {π : IntegralClosure O (IntermediateField.fixedField
      (characterOpenNormal v χ hc).toSubgroup)} (hπ : Irreducible π)
    (g : localInertiaGroup v)
    (hg : ThreeAdicPlan.uniformizerCharacter hπ
      (finiteIdealInertiaRestriction v (characterOpenNormal v χ hc) g) = 1) :
    χ g.val = 1 := by
  let N := characterOpenNormal v χ hc
  let L := IntermediateField.fixedField N.toSubgroup
  let D := IntegralClosure O L
  let : IsFractionRing D L := by
    change IsFractionRing (integralClosure O L) L
    exact integralClosure.isFractionRing_of_finite_extension Kv L
  let : SMulDistribClass Gal(L/Kv) D L := ⟨fun g b l ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  let : IsGaloisGroup Gal(L/Kv) O D :=
    IsGaloisGroup.of_isFractionRing Gal(L/Kv) O D Kv L
  let : FaithfulSMul Gal(L/Kv) D := IsGaloisGroup.faithful O
  let : CharP (ResidueField D) p :=
    charP_of_injective_ringHom (ResidueField.map (algebraMap O D)).injective p
  have h := finiteCoefficient_uniformizer_kernel (p := p) (G := Gal(L/Kv)) hπ
    ((finiteModelCharacter v χ hc).comp ((maximalIdeal D).inertia Gal(L/Kv)).subtype) hg
  exact (finiteModelCharacter_restrict v χ hc g.val).symm.trans h

end LocalRamification
