/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Integral Tate degree minus two and abelianization

The Tate comparison, the degree-one homology computation for trivial
coefficients, and the tensor unit give the canonical abelianization comparison.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory

variable (G : Type) [Group G] [Fintype G]

/-- The scalar Tate group in degree minus two is the additive abelianization. -/
def tateScalarAbelianizationEquiv :
    tateCohomology (Rep.trivial ℤ G ℤ) (-2) ≃+ Additive (Abelianization G) :=
  (((TateCohomology.isoGroupHomology (-2) 1 (by decide)).app
    (Rep.trivial ℤ G ℤ)).toLinearEquiv.toAddEquiv).trans
      ((groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).trans
        (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv)

end LocalClassFieldTheory
