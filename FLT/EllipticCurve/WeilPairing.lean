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
equivariance in addition to bilinearity. Its existence is proved in
`FLT.EllipticCurve.TorsionPairingAdapter` using translation ratios of multiplication
roots, independently of the admitted legacy map `WeierstrassCurve.weilPairing`.
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

/-- A nondegenerate alternating pairing on geometric torsion, compatible with the Galois action.
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

/-- Upgrade a bilinear torsion pairing once alternation, nondegeneracy and Galois
equivariance have been proved. Each pairing law is an explicit input. -/
def ofBilinear
    (e : (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n →+
      (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n →+
        Additive (rootsOfUnity n (AlgebraicClosure K)))
    (ha : ∀ P, e P P = 0)
    (hn : ∀ P, (∀ Q, e P Q = 0) → P = 0)
    (hg : ∀ (g : Field.absoluteGaloisGroup K) P Q,
      ((e (E.torsionGaloisRepresentation n g P)
        (E.torsionGaloisRepresentation n g Q)).toMul.val : AlgebraicClosure K) =
          g ((e P Q).toMul.val : AlgebraicClosure K)) : E.TorsionWeilPairing n where
  pairing :=
    { toFun := fun v => e (v 0) (v 1)
      map_update_add' := by
        intro _ v i x y
        fin_cases i <;> simp [map_add]
      map_update_smul' := by
        intro _ v i a x
        fin_cases i <;> simp [ZMod.map_smul]
      map_eq_zero_of_eq' := by
        intro v i j h hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · change v 0 = v 1 at h
          change e (v 0) (v 1) = 0
          rw [h]
          exact ha _
        · change v 1 = v 0 at h
          change e (v 0) (v 1) = 0
          rw [← h]
          exact ha _
        · exact (hij rfl).elim }
  nondegenerate := hn
  galois_equivariant := fun g v => hg g (v 0) (v 1)

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

/-- Over a separably closed field, prime torsion away from the characteristic has dimension two. -/
theorem finrank_prime_torsion {L : Type*} [Field L] [IsSepClosed L] [DecidableEq L]
    (E : WeierstrassCurve L) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
    (hp : (p : L) ≠ 0) : Module.finrank (ZMod p) (E.nTorsion p) = 2 := by
  obtain ⟨e⟩ := E.n_torsion_dimension hp
  let e' : E.nTorsion p ≃ₗ[ZMod p] ZMod p × ZMod p :=
    { e with map_smul' := ZMod.map_smul e }
  rw [e'.finrank_eq, Module.finrank_prod]
  simp

end WeierstrassCurve
