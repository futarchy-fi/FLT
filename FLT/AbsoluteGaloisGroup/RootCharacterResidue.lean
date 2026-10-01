/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacter
public import FLT.FreyCurve.Serre.LocalResidue
public import Mathlib.Algebra.CharP.Algebra

/-!
# The coefficient residue field for root characters

The integral closure used by root characters is the canonical valuation ring
of the local algebraic closure. Its residue field is an algebraic closure of
the completion's residue field. The comparison preserves the residue map,
and characteristic transports along that map.
-/

@[expose] public section

open NumberField IsLocalRing

namespace LocalRoot

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation "O" => v.adicCompletionIntegers K
local notation "A" => IntegralClosure O (AlgebraicClosure (v.adicCompletion K))
local notation "k₀" => ResidueField O
local notation "k" => ResidueField A

/-- Identify the integral-closure type with the canonical valuation subring. -/
noncomputable def closureValuationEquiv : A ≃+* localClosureValuation v where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Transport residues while retaining the completion's coefficient field. -/
noncomputable def residueValuationEquiv :
    k ≃ₐ[k₀] ResidueField (localClosureValuation v) where
  __ := ResidueField.mapEquiv (closureValuationEquiv v)
  commutes' x := by
    obtain ⟨x, rfl⟩ := residue_surjective x
    rfl

/-- Explicit comparison with the algebraic closure of the completion residue field. -/
noncomputable def residueClosureEquiv : k ≃ₐ[k₀] AlgebraicClosure k₀ :=
  (residueValuationEquiv v).trans (localClosureResidueEquiv v)

/-- The residue field used by root characters is algebraically closed. -/
theorem residue_isAlgClosed : IsAlgClosed k :=
  IsAlgClosed.of_ringEquiv (AlgebraicClosure k₀) k (residueClosureEquiv v).symm.toRingEquiv

/-- The root-character residue field is an algebraic closure of the completion residue field. -/
theorem residue_isAlgClosure : IsAlgClosure k₀ k :=
  ⟨residue_isAlgClosed v,
    Algebra.IsAlgebraic.of_injective (residueClosureEquiv v).toAlgHom
      (residueClosureEquiv v).injective⟩

/-- The comparison transports the already-defined residue-field inclusion. -/
@[simp] theorem residueClosureEquiv_map (x : k₀) :
    residueClosureEquiv v (residueFieldMap v x) =
      algebraMap k₀ (AlgebraicClosure k₀) x :=
  (residueClosureEquiv v).commutes x

/-- Reduction of a completion integer commutes with the comparison. -/
@[simp] theorem residueClosureEquiv_residue (x : O) :
    residueClosureEquiv v (residue A (algebraMap O A x)) =
      algebraMap k₀ (AlgebraicClosure k₀) (residue O x) :=
  residueClosureEquiv_map v (residue O x)

/-- Characteristic is transported from the completion by its injective residue-field map. -/
theorem residue_charP (p : ℕ) [CharP k₀ p] : CharP k p :=
  charP_of_injective_ringHom (residueFieldMap v).injective p

/-- Prime-to-characteristic root degrees can be checked in the completion residue field. -/
theorem residue_natCast_ne_zero_iff (n : ℕ) : (n : k) ≠ 0 ↔ (n : k₀) ≠ 0 := by
  rw [← map_natCast (residueFieldMap v), map_ne_zero]

/-- The positive prime characteristic of the completion is also that of the geometric residue. -/
theorem exists_residue_prime_characteristic :
    ∃ p : ℕ, p.Prime ∧ CharP k₀ p ∧ CharP k p := by
  exact ⟨ringChar k₀, CharP.char_is_prime k₀ _, inferInstance,
    residue_charP v (ringChar k₀)⟩

end LocalRoot
