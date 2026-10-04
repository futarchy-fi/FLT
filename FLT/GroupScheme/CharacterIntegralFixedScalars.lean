/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.UnramifiedCharacterAlgebraDescent

/-!
# Fixed scalars in the actual character splitting ring

The splitting integral closure has exactly the original integral base as its
Galois invariants. This supplies the scalar descent used by the Hopf counit.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NumberField IsLocalRing GaloisRepresentation.Extensions
namespace LocalRamification
variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
variable {k : Type} [Field k] [TopologicalSpace k] [DiscreteTopology k]
  (χ : Field.absoluteGaloisGroup (v.adicCompletion K) →* kˣ) (hc : Continuous χ)
local notation "L" => openNormalFixedField (characterOpenNormal v χ hc)
local notation "D" => IntegralClosure O L
attribute [local instance] finiteLevel_finiteDimensional finiteLevel_isDVR

/-- The character splitting field is the fraction field of its integral closure. -/
local instance characterHopfFraction : IsFractionRing D L := by
  change IsFractionRing (integralClosure O L) L
  exact integralClosure.isFractionRing_of_finite_extension Kv L

/-- Galois automorphisms respect the splitting integers acting on their fraction field. -/
local instance characterHopfDistrib : SMulDistribClass Gal(L/Kv) D L :=
  ⟨fun g b l ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩

/-- Galois-invariant elements of the integral splitting ring are original base scalars. -/
theorem finiteCharacter_fixed_scalars (s : D) (hs : ∀ g : Gal(L/Kv), g • s = s) :
    ∃ r : O, algebraMap O D r = s := by
  let : IsGaloisGroup Gal(L/Kv) O D := IsGaloisGroup.of_isFractionRing Gal(L/Kv) O D Kv L
  exact Algebra.IsInvariant.isInvariant s hs

/-- The original base embeds in the actual splitting integral closure. -/
theorem finiteCharacter_scalar_injective : Function.Injective (algebraMap O D) := by
  let := finiteCharacter_integers_faithfullyFlat v χ hc
  exact FaithfulSMul.algebraMap_injective O D

end LocalRamification
