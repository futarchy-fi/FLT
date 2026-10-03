/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Exactness between coefficient maps in Tate cohomology

This is the middle segment of the actual long exact sequence, complementary to
the two segments involving the connecting map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G]

/-- Tate cohomology sends zero coefficient maps to zero. -/
instance tateCohomology_preservesZero (n : ℤ) :
    (tateCohomologyFunctor (R := k) (G := G) n).PreservesZeroMorphisms := by
  dsimp [tateCohomologyFunctor]
  infer_instance

/-- The coefficient-map segment of the Tate long exact sequence is exact. -/
theorem tateCohomology_exact₂ {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (n : ℤ) :
    (S.map (tateCohomologyFunctor n)).Exact :=
  (TateCohomology.map_tateComplexFunctor_shortExact hS).homology_exact₂ n

end LocalClassFieldTheory
