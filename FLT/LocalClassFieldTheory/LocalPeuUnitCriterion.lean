/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ExtendedPeuUnitSubspace
public import FLT.LocalClassFieldTheory.RationalUnramifiedCharacters

/-!
# Unit annihilators for the existing valuation inertia

At number-field completions the proved kernel theorem identifies the
unramified restriction kernel with the existing local inertia group.
At rational places the complete-integers hypothesis is discharged internally.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing NumberField KummerTheory GaloisRepresentation.Extensions

variable {F : Type} [Field F] [NumberField F]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local notation "K" => v.adicCompletion F
local notation "A" => v.adicCompletionIntegers F
local notation "C" => AlgebraicClosure K

variable [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F))
  (v.adicCompletionIntegers F)] (q : ℕ) [Fact q.Prime]

/-- The prime unit subspace is the cup annihilator for actual valuation inertia. -/
theorem localPeuRamified_iff_primeUnitSubspace
    (x : LinearContinuousClass (ZMod q) Gal(C/K) (RootModule C q)) :
    IsPeuRamifiedClass (k := ZMod q) (localInertiaGroup v) (linearClassEquiv x) ↔
      x ∈ primeUnitSubspace (exists_unit_root («K» := K) (L := C) (n := q)) A := by
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField A)
  let : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField A) p⟩
  rw [← unramifiedRestriction_ker_eq_localInertia v]
  exact isPeuRamifiedClass_iff_primeUnitSubspace K C A q p x

/-- The extended unit criterion uses the same actual local inertia and original class quotient. -/
theorem localPeuRamified_iff_extendedUnitClass {ζ : Cˣ} (hζ : IsPrimitiveRoot ζ q)
    (k : Type*) [Field k] [TopologicalSpace k] [DiscreteTopology k] [Algebra (ZMod q) k]
    [FiniteDimensional (ZMod q) k]
    (x : ContinuousClass Gal(C/K) (CharacterModule (primeCyclotomicCharacter («K» := K) hζ) k)) :
    IsPeuRamifiedClass (k := k) (localInertiaGroup v) x ↔
      IsExtendedUnitClass hζ k (exists_unit_root («K» := K) (L := C) (n := q)) A x := by
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField A)
  let : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField A) p⟩
  rw [← unramifiedRestriction_ker_eq_localInertia v]
  exact isPeuRamifiedClass_iff_extendedUnitClass K C A hζ k p x

end LocalClassFieldTheory
