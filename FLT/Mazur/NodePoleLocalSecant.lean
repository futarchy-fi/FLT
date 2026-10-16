/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodePoleSecant
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Pole extraction retains coordinates in local rings at the source node

The exact secant coefficient is a unit whenever the original extraction
coefficient is a unit and the source coordinate lies in the maximal ideal.
The resulting equality holds in the local ring, including its nilpotents.
-/

public section
namespace FLT.Mazur.NodePoleSecant
variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The secant coefficient is a unit throughout a local source-node neighborhood. -/
theorem isUnit_coefficient_of_source_mem (x y a v : R)
    (hy : (y - 1) ^ 3 * v = a * y) (ha : IsUnit a)
    (hy₀ : y ∈ IsLocalRing.maximalIdeal R) : IsUnit (a - cubic x y * v) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [coefficient_node (IsLocalRing.residue R) x y a v hy
    ((IsLocalRing.residue_eq_zero_iff _).mpr hy₀)]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr ha

/-- Equal pole combinations determine the full coordinate near the source node. -/
theorem eq_of_source_mem (x y a u v : R)
    (hx : (x - 1) ^ 3 * u = a * x) (hy : (y - 1) ^ 3 * v = a * y)
    (ha : IsUnit a) (hy₀ : y ∈ IsLocalRing.maximalIdeal R) (huv : u = v) : x = y :=
  eq_of_isUnit x y a u v hx hy
    (isUnit_coefficient_of_source_mem x y a v hy ha hy₀) huv

end FLT.Mazur.NodePoleSecant
