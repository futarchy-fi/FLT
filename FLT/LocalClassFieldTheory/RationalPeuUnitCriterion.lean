/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalPeuUnitCriterion

/-!
# Prime and residual-field unit annihilators at rational places

The rational completion has complete DVR integers by the existing p-adic
comparison. Thus the actual-inertia unit criteria require no completeness
or residue-characteristic assumptions from the caller.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing NumberField KummerTheory GaloisRepresentation.Extensions

variable (p : ℕ) [Fact p.Prime]

local notation "v" => LocalCyclotomic.rationalPlace p
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
local notation "A" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "C" => AlgebraicClosure K

local instance rationalPeuIntegersComplete : IsAdicComplete (maximalIdeal A) A :=
  rationalCompletionIntegers_adicComplete p

/-- At the rational p-adic place, the prime unit subspace is the actual inertia annihilator. -/
theorem rationalPeuRamified_iff_primeUnitSubspace
    (x : LinearContinuousClass (ZMod p) Gal(C/K) (RootModule C p)) :
    IsPeuRamifiedClass (k := ZMod p) (localInertiaGroup v) (linearClassEquiv x) ↔
      x ∈ primeUnitSubspace (exists_unit_root («K» := K) (L := C) (n := p)) A :=
  localPeuRamified_iff_primeUnitSubspace v p x

/-- The residual-field unit criterion at a rational place for the independent predicate. -/
theorem rationalPeuRamified_iff_extendedUnitClass {ζ : Cˣ} (hζ : IsPrimitiveRoot ζ p)
    (k : Type*) [Field k] [TopologicalSpace k] [DiscreteTopology k] [Algebra (ZMod p) k]
    [FiniteDimensional (ZMod p) k]
    (x : ContinuousClass Gal(C/K) (CharacterModule (primeCyclotomicCharacter («K» := K) hζ) k)) :
    IsPeuRamifiedClass (k := k) (localInertiaGroup v) x ↔
      IsExtendedUnitClass hζ k (exists_unit_root («K» := K) (L := C) (n := p)) A x :=
  localPeuRamified_iff_extendedUnitClass v p hζ k x

end LocalClassFieldTheory
