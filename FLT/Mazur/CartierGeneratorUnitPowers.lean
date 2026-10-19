/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorCyclicMap
public import FLT.Mazur.CyclicUnitRelabeling

/-!
# Unit powers preserve the full Cartier subgroup divisor

Reindexing the original finite product of section ideals preserves all
multiplicities. Thus a full-level unit power is again a Cartier generator
over every base, without etaleness or distinctness assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) {P : 𝟙_ (Over S) ⟶ H.carrier}

/-- Write the actual Cartier divisor product with residue-class labels. -/
theorem IsCartierGenerator.ideal_zmod (hP : H.IsCartierGenerator P) :
    H.ideal = ∏ i : ZMod n, ((P ^ i.val) ≫ H.curveMap).left.ker := by
  rw [hP.2.2, ← Equiv.prod_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.prod_congr rfl
  intro i _
  have hi : ((ZMod.finEquiv n).toEquiv i).val = i.val := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  rw [hi]

/-- Unit powers preserve the entire Cartier generator condition on the original base. -/
theorem IsCartierGenerator.pow_unit (hP : H.IsCartierGenerator P) (u : (ZMod n)ˣ) :
    H.IsCartierGenerator (P ^ u.val.val) := by
  refine ⟨?_, hP.2.1, ?_⟩
  · rw [← pow_mul, Nat.mul_comm, pow_mul, hP.1, one_pow]
  · rw [hP.ideal_zmod H, ← Equiv.prod_comp u.mulLeft,
      ← Equiv.prod_comp (ZMod.finEquiv n).toEquiv]
    apply Finset.prod_congr rfl
    intro i _
    have hi : ((ZMod.finEquiv n).toEquiv i).val = i.val := by
      cases n with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n => rfl
    have hp := CyclicUnitRelabeling.relabeled_power P hP.1 u
      (Multiplicative.ofAdd ((ZMod.finEquiv n).toEquiv i))
    change P ^ (u.val * (ZMod.finEquiv n).toEquiv i).val =
      (P ^ u.val.val) ^ ((ZMod.finEquiv n).toEquiv i).val at hp
    rw [hi] at hp
    exact congrArg (fun Q ↦ (Q ≫ H.curveMap).left.ker) hp

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
