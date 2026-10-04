/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.AmitsurSplitContraction
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Affine faithfully flat degree-one exactness for arbitrary modules -/

@[expose] public noncomputable section
open TensorProduct
namespace Algebra.Amitsur
variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S]

/-- Faithfully flat descent makes every degree-one module cocycle a coboundary. -/
theorem faithfullyFlat_exact : Function.Exact (d₀ R S M) (d₁ R S M) :=
  Module.FaithfullyFlat.lTensor_reflects_exact R S _ _ (baseChanged_exact R S M)

/-- An actual correcting cochain exists for each cocycle in the displayed tensor module. -/
theorem exists_cocycle_correction (z : S ⊗[R] (S ⊗[R] M)) (hz : d₁ R S M z = 0) :
    ∃ w : S ⊗[R] M, d₀ R S M w = z :=
  (faithfullyFlat_exact R S M z).mp hz

end Algebra.Amitsur
