/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Coordinate algebra of a Kummer extension

For a unit `u` and a positive integer `n`, the components of the Kummer
extension of `ℤ/nℤ` by `μₙ` have equations `X ^ n = u ^ i`.
This file constructs their coordinate algebra and proves it is finite free.
The module-theoretic finite-flat property does not supply a Hopf structure.
-/

@[expose] public section

open Polynomial

namespace KummerAlgebra

variable (R : Type*) [CommRing R] (n : ℕ) (u : Rˣ)

/-- The equation of component `i` of the Kummer extension. -/
noncomputable def equation (i : Fin n) : R[X] := X ^ n - C ((u : R) ^ i.val)

/-- The coordinate ring of one Kummer component. -/
abbrev Component (i : Fin n) := AdjoinRoot (equation R n u i)

/-- The coordinate ring of the disjoint union of the Kummer components. -/
abbrev Coordinate := (i : Fin n) → Component R n u i

/-- Every component equation is monic when the torsion order is positive. -/
theorem equation_monic (hn : 0 < n) (i : Fin n) : (equation R n u i).Monic :=
  monic_X_pow_sub_C _ (ne_of_gt hn)

/-- A Kummer component is a free module over the coefficient ring. -/
theorem component_free (hn : 0 < n) (i : Fin n) : Module.Free R (Component R n u i) :=
  (equation_monic R n u hn i).free_adjoinRoot

/-- A Kummer component is a finite module over the coefficient ring. -/
theorem component_finite (hn : 0 < n) (i : Fin n) :
    Module.Finite R (Component R n u i) :=
  (equation_monic R n u hn i).finite_adjoinRoot

/-- The complete Kummer coordinate ring is free over the coefficient ring. -/
theorem coordinate_free (hn : 0 < n) : Module.Free R (Coordinate R n u) := by
  let _ (i : Fin n) := component_free R n u hn i
  infer_instance

/-- The complete Kummer coordinate ring is finite over the coefficient ring. -/
theorem coordinate_finite (hn : 0 < n) : Module.Finite R (Coordinate R n u) := by
  let _ (i : Fin n) := component_finite R n u hn i
  infer_instance

/-- The Kummer coordinate ring satisfies the module-theoretic finite-flat condition,
including when `n` is not invertible in the coefficient ring. -/
theorem coordinate_isFiniteFlat (hn : 0 < n) :
    HopfAlgebra.IsFiniteFlat R (Coordinate R n u) := by
  let _ := coordinate_free R n u hn
  let _ := coordinate_finite R n u hn
  exact ⟨⟩

end KummerAlgebra
