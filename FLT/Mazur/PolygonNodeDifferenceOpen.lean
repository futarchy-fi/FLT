/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonNodeBranches

/-!
# The full principal node boundary is covered by its two Laurent branches

For a unit a, the basic open of a*(y-x) is exactly the union of the two
punctured branches. This describes the full boundary used by the divided
charts and retains both branches.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.PolygonNodeBranches
open PolygonNodeEqualizer PolygonNodeLocalization
variable {R : Type*} [CommRing R]

/-- The ordered coordinate difference is nonzero precisely off the common node. -/
theorem difference_basicOpen :
    PrimeSpectrum.basicOpen (y - x : A (R := R)) =
      PrimeSpectrum.basicOpen x ⊔ PrimeSpectrum.basicOpen y := by
  ext p
  change y - x ∉ p.asIdeal ↔ x ∉ p.asIdeal ∨ y ∉ p.asIdeal
  have hxy : x (R := R) ∈ p.asIdeal ∨ y ∈ p.asIdeal :=
    p.isPrime.mem_or_mem (by rw [x_mul_y]; exact p.asIdeal.zero_mem)
  constructor
  · intro h
    by_contra hn
    have hx : x (R := R) ∈ p.asIdeal := by tauto
    have hy : y (R := R) ∈ p.asIdeal := by tauto
    exact h (p.asIdeal.sub_mem hy hx)
  · intro h hd
    rcases hxy with hx | hy
    · have hy : y (R := R) ∈ p.asIdeal := by
        simpa only [sub_add_cancel] using p.asIdeal.add_mem hd hx
      exact h.elim (fun hn => hn hx) (fun hn => hn hy)
    · have hx : x (R := R) ∈ p.asIdeal := by
        simpa only [sub_sub_cancel] using p.asIdeal.sub_mem hy hd
      exact h.elim (fun hn => hn hx) (fun hn => hn hy)

/-- A unit coefficient does not change the complete two-branch boundary. -/
theorem scaled_difference_basicOpen (a : Rˣ) :
    PrimeSpectrum.basicOpen (algebraMap R (A (R := R)) (↑a : R) * (y - x)) =
      PrimeSpectrum.basicOpen x ⊔ PrimeSpectrum.basicOpen y := by
  have h : PrimeSpectrum.basicOpen (algebraMap R (A (R := R)) (↑a : R)) = ⊤ := by
    ext p
    change algebraMap R (A (R := R)) (↑a : R) ∉ p.asIdeal ↔ True
    rw [iff_true]
    intro hm
    exact p.isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hm (a.isUnit.map (algebraMap R (A (R := R)))))
  rw [PrimeSpectrum.basicOpen_mul, h, top_inf_eq, difference_basicOpen]

/-- Both original Laurent branches cover the whole scaled-difference principal open. -/
theorem branches_cover_difference (a : Rˣ) :
    Set.range (left R) ∪ Set.range (right R) =
      (PrimeSpectrum.basicOpen
        (algebraMap R (A (R := R)) (↑a : R) * (y - x)) : Set (PrimeSpectrum (A (R := R)))) := by
  rw [range_left, range_right, scaled_difference_basicOpen]
  rfl

end FLT.Mazur.PolygonNodeBranches
