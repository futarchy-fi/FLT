/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothCyclicDivisorSymmetry

/-!
# Cyclic relabeling preserves the full orbit ideal

An automorphism permutes all cyclic labels, hence all factors of the Cartier
ideal. Coincident sections retain their multiplicities in this permutation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (e : MulAut (Multiplicative (ZMod n)))

/-- Multiplicative cyclic labels enumerate exactly the original factors. -/
theorem cyclicMarkingIdeal_multiplicative : E.cyclicMarkingIdeal φ =
    ∏ i : Multiplicative (ZMod n), (φ i ≫ E.inclusion).left.ker := by
  rw [cyclicMarkingIdeal_zmod]
  exact Equiv.prod_comp (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n))
    (fun i ↦ (φ i ≫ E.inclusion).left.ker)

/-- Relabeling preserves the entire ideal, without assuming distinct cyclic sections. -/
theorem cyclicMarkingIdeal_relabel :
    E.cyclicMarkingIdeal (φ.comp e.toMonoidHom) = E.cyclicMarkingIdeal φ := by
  rw [cyclicMarkingIdeal_multiplicative, cyclicMarkingIdeal_multiplicative]
  exact Equiv.prod_comp e.toEquiv (fun i ↦ (φ i ≫ E.inclusion).left.ker)

end FLT.Mazur.GeneralizedEllipticCurve
