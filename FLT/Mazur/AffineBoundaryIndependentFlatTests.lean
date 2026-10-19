/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryFlatScalarEquations

/-!
# Independent flat scalar branches for finite completeness tests

Each test may use its own flat scalar branch and its own branch function.
The branches only need points over the same original scalar prime. Descending
each singleton test and then assembling the original kernels constructs a
single original denominator for the full finite ideal power.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)
  (Y : a → Scheme) (g : ∀ t, Y t ⟶ Spec (.of T))
  [∀ t, Flat (g t)] [∀ t, LocallyOfFinitePresentation (g t)]
  (P : PrimeSpectrum T) (y : ∀ t, Y t) (hy : ∀ t, g t (y t) = P)
  (x : ∀ t, Γ(Y t, ⊤)) (hx : ∀ t, y t ∈ (Y t).basicOpen (x t))
include hy hx
local notation "π" => boundaryScalarProjection s κ

/-- Different tests may descend through entirely different full Cartesian scalar branches. -/
theorem boundaryScalar_mem_of_independent_flat_tests
    (he : ∀ t, ∃ k : ℕ,
      ((pullback.fst π (g t)).appTop (boundaryCoordinate s κ t.val)) ^ k *
        (pullback.snd π (g t)).appTop (x t) = 0) :
    P ∈ boundaryScalarNilpotenceOpen s κ a := by
  classical
  apply (boundaryScalar_mem_iff_testKernels s κ a P).mpr
  intro t ht
  let i : a := ⟨t, ht⟩
  have hsingle := boundaryScalar_mem_of_flat_equations s κ {t} (g i) (y i) (x i) (hx i)
    (by
      intro b hb
      obtain rfl := Finset.mem_singleton.mp hb
      exact he i)
  rw [hy i] at hsingle
  exact (boundaryScalar_mem_iff_testKernels s κ {t} P).mp hsingle t
    (Finset.mem_singleton_self t)

/-- Independent branch denominators yield one original scalar annihilating the entire test power. -/
theorem boundaryScalar_denominator_of_independent_flat_tests
    (he : ∀ t, ∃ k : ℕ,
      ((pullback.fst π (g t)).appTop (boundaryCoordinate s κ t.val)) ^ k *
        (pullback.snd π (g t)).appTop (x t) = 0) :
    ∃ (order : ℕ) (r : T), r ∉ P.asIdeal ∧
      boundaryScalarHom s κ r ∈ ((boundaryTestIdeal s κ a) ^ order).annihilator :=
  (mem_boundaryScalarNilpotenceOpen s κ a P).mp
    (boundaryScalar_mem_of_independent_flat_tests s κ a Y g P y hy x hx he)

end FLT.Mazur.AffineScalarBoundaryNilpotence
