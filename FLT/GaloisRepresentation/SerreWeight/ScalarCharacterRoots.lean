/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.ScalarCharacterFrobenius
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Realizing extracted scalar characters as roots of unity

A finite scalar field embedded in a coefficient field gives a root-valued
character without changing its kernel or collapsing its Frobenius orbit.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.SerreWeight

variable {F k G : Type*} [Field F] [Finite F] [Field k] [Group G]

/-- Embed all units of the finite scalar field into roots of the prescribed order. -/
def scalarUnitsToRoots (ε : F →+* k) {n : ℕ} (hcard : Nat.card F - 1 = n) :
    Fˣ →* rootsOfUnity n k := by
  classical
  let := Fintype.ofFinite F
  refine (Units.map ε.toMonoidHom).codRestrict _ fun a ↦ ?_
  rw [mem_rootsOfUnity, ← map_pow]
  have hn : Fintype.card Fˣ = n := by
    simpa only [Fintype.card_units, Nat.card_eq_fintype_card] using hcard
  rw [← hn, pow_card_eq_one, map_one]

/-- Passing to roots of unity retains every distinct scalar. -/
theorem scalarUnitsToRoots_injective (ε : F →+* k) {n : ℕ}
    (hcard : Nat.card F - 1 = n) : Function.Injective (scalarUnitsToRoots ε hcard) := by
  intro a b h
  apply Units.ext
  apply ε.injective
  exact congrArg (fun x : rootsOfUnity n k ↦ ((x : kˣ) : k)) h

/-- The root-valued character has exactly the original scalar-character kernel. -/
theorem scalarUnitsToRoots_comp_ker (ε : F →+* k) {n : ℕ}
    (hcard : Nat.card F - 1 = n) (χ : G →* Fˣ) :
    ((scalarUnitsToRoots ε hcard).comp χ).ker = χ.ker := by
  ext g
  change scalarUnitsToRoots ε hcard (χ g) = 1 ↔ χ g = 1
  rw [← (scalarUnitsToRoots ε hcard).map_one]
  exact (scalarUnitsToRoots_injective ε hcard).eq_iff

/-- A coefficient embedding cannot make two Frobenius-conjugate characters equal. -/
theorem scalarUnitsToRoots_comp_frobenius_ne (ε : F →+* k) {n p : ℕ}
    (hcard : Nat.card F - 1 = n) (χ : G →* Fˣ) (hne : χ ^ p ≠ χ) :
    ((scalarUnitsToRoots ε hcard).comp χ) ^ p ≠ (scalarUnitsToRoots ε hcard).comp χ := by
  intro h
  apply hne
  apply MonoidHom.ext
  intro g
  apply scalarUnitsToRoots_injective ε hcard
  simpa only [MonoidHom.pow_apply, MonoidHom.comp_apply, map_pow] using
    DFunLike.congr_fun h g

end GaloisRepresentation.SerreWeight
