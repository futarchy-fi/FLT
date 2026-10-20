/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableCobarCoordinates
public import Mathlib.Tactic.Abel

/-!+# Integral contraction of diagonalizable two-cocycles

Extracting the trivial character in the third variable turns the actual
associativity equation into a coboundary formula. The correction is unique:
there are no additive primitive functions on a diagonalizable group. Neither
statement requires the order of its character group to be invertible.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DiagonalizableCobar

variable (R M G : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Zero G]

private theorem slice_single {A B : Type*} [Zero B] [DecidableEq B] (a : A) (b : B) (m : M) :
    Finsupp.lcomapDomain (R := R) (fun c : A ↦ (c, (0 : B)))
      (fun _ _ h ↦ congrArg Prod.fst h) (Finsupp.single (a, b) m) =
        if b = 0 then Finsupp.single a m else 0 := by
  classical
  ext c
  change Finsupp.single (a, b) m (c, 0) = _
  by_cases hb : b = 0 <;> simp [Finsupp.single_apply, hb]

/-- Contraction of the first pair projection is the identity. -/
theorem contractThree_front :
    (contractThree R M G).comp (front R M G) = LinearMap.id := by
  apply LinearMap.ext
  intro p
  apply Finsupp.ext
  intro a
  exact Finsupp.mapDomain_apply_of_injective (fun _ _ h ↦ congrArg Prod.fst h) p a

/-- Multiplication of the first pair commutes with extraction in the third variable. -/
theorem contractThree_leftProduct :
    (contractThree R M G).comp (leftProduct R M G) =
      (diagonal R M G).comp (contract R M G) := by
  classical
  apply Finsupp.lhom_ext
  intro ⟨a, b⟩ m
  simp only [LinearMap.comp_apply, contractThree, leftProduct, diagonal, contract,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, slice_single]
  by_cases hb : b = 0 <;> simp [hb, Finsupp.mapDomain_single]

/-- Projection onto the last pair leaves a second-factor correction. -/
theorem contractThree_back :
    (contractThree R M G).comp (back R M G) =
      (second R M G).comp (contract R M G) := by
  classical
  apply Finsupp.lhom_ext
  intro ⟨a, b⟩ m
  simp only [LinearMap.comp_apply, contractThree, back, second, contract,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, slice_single]
  by_cases hb : b = 0 <;> simp [hb, Finsupp.mapDomain_single]

/-- Multiplication of the last pair leaves a first-factor correction. -/
theorem contractThree_rightProduct :
    (contractThree R M G).comp (rightProduct R M G) =
      (first R M G).comp (contract R M G) := by
  classical
  apply Finsupp.lhom_ext
  intro ⟨a, b⟩ m
  simp only [LinearMap.comp_apply, contractThree, rightProduct, first, contract,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, slice_single]
  by_cases hb : b = 0 <;> simp [hb, Finsupp.mapDomain_single]

/-- Every full diagonalizable two-cocycle is its explicit integral coboundary. -/
theorem cocycle_eq_boundary (p : G × G →₀ M)
    (hp : front R M G p + leftProduct R M G p =
      back R M G p + rightProduct R M G p) :
    p = boundary R M G (contract R M G p) := by
  have h := congrArg (contractThree R M G) hp
  simp only [map_add, ← LinearMap.comp_apply, contractThree_front,
    contractThree_leftProduct, contractThree_back, contractThree_rightProduct,
    LinearMap.id_apply] at h
  simp only [boundary, LinearMap.sub_apply, LinearMap.add_apply]
  rw [eq_sub_iff_add_eq]
  exact h.trans (add_comm _ _)

/-- Taking one coefficient recovers every correction from its coboundary. -/
theorem contract_boundary :
    (contract R M G).comp (boundary R M G) = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext
  intro a m
  ext b
  simp only [LinearMap.comp_apply, boundary_single, map_sub, map_add,
    Finsupp.sub_apply, Finsupp.add_apply, contract_apply, LinearMap.id_apply]
  by_cases ha : a = 0 <;> simp [Finsupp.single_apply, ha]

/-- There are no nonzero additive primitive functions, even at noninvertible orders. -/
theorem boundary_injective : Function.Injective (boundary R M G) := by
  intro p q h
  have hc := congrArg (contract R M G) h
  simpa only [← LinearMap.comp_apply, contract_boundary, LinearMap.id_apply] using hc

/-- The original cocycle determines a unique correction in the full character algebra. -/
theorem existsUnique_correction (p : G × G →₀ M)
    (hp : front R M G p + leftProduct R M G p =
      back R M G p + rightProduct R M G p) :
    ∃! q, boundary R M G q = p := by
  refine ⟨contract R M G p, (cocycle_eq_boundary R M G p hp).symm, ?_⟩
  intro q hq
  exact boundary_injective R M G (hq.trans (cocycle_eq_boundary R M G p hp))

end FLT.Mazur.DiagonalizableCobar
