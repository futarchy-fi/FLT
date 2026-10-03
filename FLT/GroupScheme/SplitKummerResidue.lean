/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PrimitiveRootCoordinates
public import FLT.GroupScheme.SplitKummerGeneralPointLaw
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! # Additive residue coordinates on the split Kummer geometric points -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable (R K : Type) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Reading root exponents and components gives two residue coordinates. -/
def splitKummerResidueEquiv :
    (generalSplitKummerModel R K p n).Points ≃ ZMod (p ^ n) × ZMod (p ^ n) := by
  let : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let e := primitiveRootCoordinates (algebraicClosurePrimitiveRoot_spec K (p ^ n))
  refine (generalSplitKummerCoordinates R K p n).trans
    { toFun := fun x ↦ (e.symm (Additive.ofMul ⟨x.val.2, x.property⟩),
        ZMod.finEquiv (p ^ n) x.val.1)
      invFun := fun x ↦ ⟨((ZMod.finEquiv (p ^ n)).symm x.2,
        (e x.1).toMul.val), (e x.1).toMul.property⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    simp
  · intro x
    change (e.symm (e x.1), _) = x
    simp

/-- The coordinates preserve addition of the actual Hopf-algebra points. -/
theorem splitKummerResidueEquiv_add (x y : (generalSplitKummerModel R K p n).Points) :
    splitKummerResidueEquiv R K p n (x + y) =
      splitKummerResidueEquiv R K p n x + splitKummerResidueEquiv R K p n y := by
  let : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have h := generalSplitKummerCoordinates_add R K p n x y
  let e := primitiveRootCoordinates (algebraicClosurePrimitiveRoot_spec K (p ^ n))
  apply Prod.ext
  · change e.symm _ = e.symm _ + e.symm _
    rw [← map_add]
    congr 1
    apply Subtype.ext
    exact congrArg Prod.snd h
  · change ZMod.finEquiv (p ^ n) _ =
      ZMod.finEquiv (p ^ n) _ + ZMod.finEquiv (p ^ n) _
    rw [← map_add]
    congr 1
    exact congrArg Prod.fst h

/-- Actual geometric points identified additively with the standard residues. -/
def splitKummerResidue :
    (generalSplitKummerModel R K p n).Points ≃+ ZMod (p ^ n) × ZMod (p ^ n) :=
  { splitKummerResidueEquiv R K p n with
    map_add' := splitKummerResidueEquiv_add R K p n }

/-- Local Galois acts cyclotomically on the first residue and fixes the second. -/
theorem splitKummerResidue_smul
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : (generalSplitKummerModel R K p n).Points) :
    splitKummerResidue R K p n (g • x) =
      (PadicInt.toZModPow n (cyclotomicCharacter (AlgebraicClosure K) p g.toRingEquiv).val *
        (splitKummerResidue R K p n x).1, (splitKummerResidue R K p n x).2) := by
  let : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let e := primitiveRootCoordinates (algebraicClosurePrimitiveRoot_spec K (p ^ n))
  let c := PadicInt.toZModPow n (cyclotomicCharacter (AlgebraicClosure K) p g.toRingEquiv).val
  have h := generalSplitKummerCoordinates_smul R K p n g x
  apply Prod.ext
  · change e.symm _ = c * e.symm _
    apply e.injective
    rw [e.apply_symm_apply, ← ZMod.natCast_zmod_val c, primitiveRootCoordinates_pow]
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (generalSplitKummerCoordinates R K p n (g • x)).val.2 = _
    rw [h]
    apply Units.ext
    exact cyclotomicCharacter.spec p g.toRingEquiv _
      (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg Units.val (generalSplitKummerCoordinates R K p n x).property)
  · change ZMod.finEquiv (p ^ n) _ = ZMod.finEquiv (p ^ n) _
    rw [h]

end ThreeAdicPlan
