/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIdealIso
public import FLT.Mazur.RationalCyclicModuliPoint
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Changing the rational cyclic generator

Multiplying the generator by an integer coprime to its order permutes the
actual rational orbit ideals. The resulting subgroups are compatibly
isomorphic, so they determine the same ample cyclic moduli point.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.GeneralizedEllipticCurve

open FiniteSubgroup

variable {K : Type} [Field K] (E : GeneralizedEllipticCurve (Spec (.of K)))
  {n : ℕ} [NeZero n] (P : 𝟙_ (Over (Spec (.of K))) ⟶ E.group) (ho : orderOf P = n)

/-- The actual subgroup ideal as a product indexed by residue classes. -/
theorem rationalCyclicSubgroup_ideal_zmod :
    (E.rationalCyclicSubgroup P ho).ideal =
      ∏ i : ZMod n, ((P ^ i.val) ≫ E.inclusion).left.ker := by
  rw [E.rationalCyclicSubgroup_ideal P ho, ← Equiv.prod_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.prod_congr rfl
  intro i _
  have hv : ((ZMod.finEquiv n).toEquiv i).val = i.val := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  have he : (E.rationalCyclicGenerator P ho ^ i.val) ≫
      (E.rationalCyclicSubgroup P ho).curveMap = (P ^ i.val) ≫ E.inclusion := by
    rw [FiniteSubgroup.curveMap, ← Category.assoc, MonObj.pow_comp,
      E.rationalCyclicGenerator_inclusion P ho]
  simpa only [hv] using congrArg (fun f ↦ f.left.ker) he

include ho in
omit [NeZero n] in
/-- A coprime power of the original generator still has the specified exact order. -/
theorem rationalCyclicPower_order (k : ℕ) (hk : k.Coprime n) : orderOf (P ^ k) = n := by
  have hc : (orderOf P).Coprime k := by simpa only [ho] using hk.symm
  exact hc.orderOf_pow.trans ho

/-- Coprime generator changes leave the actual closed subgroup ideal unchanged. -/
theorem rationalCyclicSubgroup_ideal_pow (k : ℕ) (hk : k.Coprime n)
    (hok : orderOf (P ^ k) = n) :
    (E.rationalCyclicSubgroup (P ^ k) hok).ideal = (E.rationalCyclicSubgroup P ho).ideal := by
  rw [E.rationalCyclicSubgroup_ideal_zmod (P ^ k) hok, E.rationalCyclicSubgroup_ideal_zmod P ho]
  conv_rhs => rw [← Equiv.prod_comp (ZMod.unitOfCoprime k hk).mulLeft]
  apply Finset.prod_congr rfl
  intro i _
  have hm : (ZMod.unitOfCoprime k hk).mulLeft i = ((k * i.val : ℕ) : ZMod n) := by
    change (ZMod.unitOfCoprime k hk : ZMod n) * i = _
    rw [ZMod.coe_unitOfCoprime, Nat.cast_mul, ZMod.natCast_zmod_val]
  have hp : P ^ ((ZMod.unitOfCoprime k hk).mulLeft i).val = (P ^ k) ^ i.val := by
    rw [hm, ZMod.val_natCast, ← pow_mul]
    simpa only [ho] using pow_mod_orderOf P (k * i.val)
  exact congrArg (fun Q ↦ (Q ≫ E.inclusion).left.ker) hp.symm

/-- Coprime changes give an actual compatible isomorphism of the constructed subgroups. -/
def rationalCyclicSubgroupPowerIso (k : ℕ) (hk : k.Coprime n)
    (hok : orderOf (P ^ k) = n) :
    CompatibleIso (E.rationalCyclicSubgroup (P ^ k) hok) (E.rationalCyclicSubgroup P ho) :=
  compatibleIsoOfIdealEq _ _ (E.rationalCyclicSubgroup_ideal_pow P ho k hk hok)

/-- The actual ample cyclic moduli point is independent of a coprime generator change. -/
theorem rationalCyclicModuliPoint_pow [SmoothOfRelativeDimension 1 E.curve.hom]
    [GeometricallyIntegral E.curve.hom] (k : ℕ) (hk : k.Coprime n)
    (hok : orderOf (P ^ k) = n) :
    E.rationalCyclicModuliPoint (P ^ k) hok = E.rationalCyclicModuliPoint P ho :=
  Quotient.sound ⟨E.rationalCyclicSubgroupPowerIso P ho k hk hok⟩

end FLT.Mazur.GeneralizedEllipticCurve
