/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Torsion
public import FLT.Mathlib.LinearAlgebra.Alternating.Determinant
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# A checked interface for the Weil pairing

`WeierstrassCurve.TorsionWeilPairing` records alternation, nondegeneracy and Galois
equivariance in addition to bilinearity. Its existence is a separate geometric
obligation; the admitted bilinear map `WeierstrassCurve.weilPairing` does not
currently establish this contract.
-/

@[expose] public section

namespace rootsOfUnity

variable (L : Type*) [Field L] (n : ℕ)

/-- Roots of unity, written additively, form a module over `ZMod n`. -/
instance zmodModule : Module (ZMod n) (Additive (rootsOfUnity n L)) :=
  AddCommGroup.zmodModule fun x => by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (mem_rootsOfUnity n x.toMul.val).mp x.toMul.property

/-- Scalar multiplication on roots of unity is exponentiation by a residue representative. -/
theorem coe_smul [NeZero n] (a : ZMod n) (x : Additive (rootsOfUnity n L)) :
    ((a • x).toMul.val : L) = (x.toMul.val : L) ^ a.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul]
  rfl

end rootsOfUnity

namespace WeierstrassCurve

variable {K : Type*} [Field K] (E : WeierstrassCurve K)
  [DecidableEq (AlgebraicClosure K)] (n : ℕ)

/-- A perfect alternating pairing on geometric torsion, compatible with the Galois action.
The linear target is the additive form of the group of roots of unity. -/
structure TorsionWeilPairing where
  /-- The alternating bilinear map on geometric torsion. -/
  pairing : (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n [⋀^Fin 2]→ₗ[ZMod n]
    Additive (rootsOfUnity n (AlgebraicClosure K))
  /-- The left radical vanishes; alternation then gives the same property on the right. -/
  nondegenerate : ∀ P, (∀ Q, pairing ![P, Q] = 0) → P = 0
  /-- Applying a field automorphism to both points applies it to the pairing value. -/
  galois_equivariant : ∀ (g : Field.absoluteGaloisGroup K) v,
    ((pairing (E.torsionGaloisRepresentation n g ∘ v)).toMul.val : AlgebraicClosure K) =
      g ((pairing v).toMul.val : AlgebraicClosure K)

namespace TorsionWeilPairing

variable {E n} (w : E.TorsionWeilPairing n)

/-- Nondegeneracy forces the pairing on a nonzero torsion module to be nonzero. -/
theorem pairing_ne_zero
    [Nontrivial ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n)] :
    w.pairing ≠ 0 := by
  intro h
  obtain ⟨P, hP⟩ := exists_ne
    (0 : (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n)
  apply hP
  exact w.nondegenerate P fun Q => by rw [h]; rfl

/-- Galois equivariance makes the pairing a similitude with cyclotomic multiplier. -/
theorem map_eq_cyclotomic_smul [NeZero n]
    (hn : Nat.card (rootsOfUnity n (AlgebraicClosure K)) = n)
    (g : Field.absoluteGaloisGroup K) v :
    w.pairing (E.torsionGaloisRepresentation n g ∘ v) =
      (modularCyclotomicCharacter (AlgebraicClosure K) hn g.toRingEquiv : ZMod n) •
        w.pairing v := by
  apply Additive.toMul.injective
  apply rootsOfUnity.coe_injective
  dsimp only
  rw [w.galois_equivariant, rootsOfUnity.coe_smul]
  exact modularCyclotomicCharacter.spec _ hn g.toRingEquiv (w.pairing v).toMul.property

end TorsionWeilPairing

end WeierstrassCurve
