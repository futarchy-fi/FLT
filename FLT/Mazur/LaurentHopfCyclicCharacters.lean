/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ToricHopfQuotientCoordinates
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The finite cyclic character group of a Laurent Hopf quotient

The generator is the original Laurent coordinate, not an arbitrarily chosen
cyclic generator. Its character group has cardinality equal to the dimension
of the original finite coordinate algebra.
-/

@[expose] public noncomputable section

open scoped LaurentPolynomial

namespace FLT.Mazur.LaurentHopfCyclicCharacters

open ToricHopfCharacterKernel

variable {K A : Type*} [Field K] [Ring A] [HopfAlgebra K A]
  (f : K[T;T⁻¹] →ₐc[K] A)

/-- The given Laurent map written with multiplicative integer characters. -/
def multiplicativeMap : MonoidAlgebra K (Multiplicative ℤ) →ₐc[K] A :=
  f.comp (AddMonoidAlgebra.toMultiplicativeBialgEquiv K K ℤ).symm.toBialgHom

/-- The character group cut out by the original full coordinate map. -/
abbrev Characters := Multiplicative ℤ ⧸ kernel (multiplicativeMap f)

/-- The original Laurent coordinate defines the specified generator. -/
def generator : Characters f := QuotientGroup.mk (Multiplicative.ofAdd 1)

/-- Every surviving character is a power of the original Laurent coordinate. -/
theorem generator_generates (x : Characters f) : x ∈ Subgroup.zpowers (generator f) := by
  induction x using Quotient.inductionOn' with
  | h i =>
    refine ⟨i.toAdd, ?_⟩
    change (QuotientGroup.mk' (kernel (multiplicativeMap f)))
      (Multiplicative.ofAdd 1) ^ i.toAdd = _
    rw [← map_zpow]
    apply congrArg (QuotientGroup.mk' (kernel (multiplicativeMap f)))
    change Multiplicative.ofAdd (i.toAdd • (1 : ℤ)) = i
    simp

/-- Finite-dimensional subgroup coordinates give a finite character quotient. -/
theorem characters_finite [Module.Finite K A] : Finite (Characters f) :=
  quotient_finite (multiplicativeMap f)

/-- Surjectivity retains all of the original coordinate algebra in multiplicative notation. -/
theorem multiplicativeMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (multiplicativeMap f) :=
  hf.comp (AddMonoidAlgebra.toMultiplicativeBialgEquiv K K ℤ).symm.surjective

/-- The character count is the rank of the original subgroup coordinate algebra. -/
theorem characters_card (hf : Function.Surjective f) :
    Nat.card (Characters f) = Module.finrank K A := by
  let e := quotientCoordinatesEquiv (multiplicativeMap f) (multiplicativeMap_surjective f hf)
  exact (Module.finrank_eq_nat_card_basis
    ((MonoidAlgebra.basis (Characters f) K).map e.toAlgEquiv.toLinearEquiv)).symm

/-- A finite Hopf quotient has strictly positive dimension. -/
theorem finrank_pos [Module.Finite K A] (hf : Function.Surjective f) :
    0 < Module.finrank K A := by
  let _ := characters_finite f
  rw [← characters_card f hf]
  exact Nat.card_pos

/-- The canonical cyclic character equivalence preserves the specified coordinate. -/
def cyclicEquiv (hf : Function.Surjective f) :
    Multiplicative (ZMod (Module.finrank K A)) ≃* Characters f :=
  zmodMulEquivOfGenerator (generator_generates f) (characters_card f hf)

/-- Every integer character is preserved, not only the chosen generator. -/
theorem cyclicEquiv_intCast (hf : Function.Surjective f) (i : ℤ) :
    cyclicEquiv f hf (Multiplicative.ofAdd (i : ZMod (Module.finrank K A))) =
      QuotientGroup.mk (Multiplicative.ofAdd i) := by
  rw [cyclicEquiv, zmodMulEquivOfGenerator_apply_ofAdd_intCast]
  change (QuotientGroup.mk' (kernel (multiplicativeMap f)))
    (Multiplicative.ofAdd 1) ^ i = _
  rw [← map_zpow]
  apply congrArg (QuotientGroup.mk' (kernel (multiplicativeMap f)))
  change Multiplicative.ofAdd (i • (1 : ℤ)) = _
  simp

end FLT.Mazur.LaurentHopfCyclicCharacters
