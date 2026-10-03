/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexGaloisAction
public import Mathlib.FieldTheory.Galois.Infinite

/-! # Finite algebraic Galois orbits and their actual invariant sums -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Every actual algebraic orbit is finite, since it lies among minimal-polynomial roots. -/
theorem padicGalois_orbit_finite (a : PadicAlgCl p) :
    (MulAction.orbit (PadicGalois p) a).Finite := by
  refine (Polynomial.rootSet_finite (minpoly ℚ_[p] a) (PadicAlgCl p)).subset ?_
  rintro b ⟨σ, rfl⟩
  rw [Polynomial.mem_rootSet_of_ne (minpoly.ne_zero (Algebra.IsIntegral.isIntegral a))]
  change Polynomial.aeval (σ a) (minpoly ℚ_[p] a) = 0
  rw [← minpoly.algEquiv_eq σ a]
  exact minpoly.aeval _ _

/-- The finite type is the actual orbit, not a selected list of conjugates. -/
instance instFintypePadicGaloisOrbit (a : PadicAlgCl p) :
    Fintype (MulAction.orbit (PadicGalois p) a) := (padicGalois_orbit_finite p a).fintype

/-- Every orbit has positive cardinality because it contains its original element. -/
theorem padicGalois_orbit_card_pos (a : PadicAlgCl p) :
    0 < Fintype.card (MulAction.orbit (PadicGalois p) a) := by
  exact Fintype.card_pos_iff.mpr ⟨⟨a, MulAction.mem_orbit_self a⟩⟩

/-- The unnormalized sum of all distinct conjugates. -/
def padicGaloisOrbitSum (a : PadicAlgCl p) : PadicAlgCl p :=
  ∑ b : MulAction.orbit (PadicGalois p) a, (b : PadicAlgCl p)

/-- Automorphisms permute the actual orbit, so its sum is fixed. -/
theorem padicGaloisOrbitSum_fixed (a : PadicAlgCl p) (σ : PadicGalois p) :
    σ (padicGaloisOrbitSum p a) = padicGaloisOrbitSum p a := by
  unfold padicGaloisOrbitSum
  rw [map_sum]
  exact Fintype.sum_equiv (MulAction.toPerm σ) _ _ (fun _ ↦ rfl)

/-- Algebraic fixed-field descent puts the actual orbit sum in Q_p. -/
theorem padicGaloisOrbitSum_mem_range (a : PadicAlgCl p) :
    padicGaloisOrbitSum p a ∈ Set.range (algebraMap ℚ_[p] (PadicAlgCl p)) :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr (padicGaloisOrbitSum_fixed p a)

end PadicHodgeTheory
