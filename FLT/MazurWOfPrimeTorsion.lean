/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.MazurW

/-!
# Sufficient conditions for the Mazur torsion exclusion

Excluding large prime-order points implies the exclusion in `mazur_W`.
A finite torsion subgroup with a sufficiently small cardinality also excludes
an embedded `(ℤ/2ℤ)² × ℤ/ℓℤ` in any additive commutative group.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

/-- Rational elliptic curves have no point of prime order at least `17`. -/
def NoLargePrimeTorsion : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → 17 ≤ ℓ →
    ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
      ¬ ∃ P : (E⁄ℚ).Point, addOrderOf P = ℓ

/-- The large-prime torsion exclusion suffices for the conclusion of `mazur_W`. -/
theorem mazur_W_of_noLargePrimeTorsion (h : NoLargePrimeTorsion)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ17 : 17 ≤ ℓ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ((ZMod 2 × ZMod 2) × ZMod ℓ) →+ (E⁄ℚ).Point,
      Function.Injective f := by
  rintro ⟨f, hf⟩
  apply h ℓ hℓ hℓ17 E inferInstance
  refine ⟨f (0, 1), ?_⟩
  rw [addOrderOf_injective f hf]
  simp [Prod.addOrderOf, ZMod.addOrderOf_one]

/-- A finite torsion subgroup of cardinality at most `B < 4 * ℓ` cannot contain
an embedded `(ℤ/2ℤ)² × ℤ/ℓℤ`. Primality of `ℓ` is unnecessary. -/
theorem no_fullTwoTimesPrime_of_torsion_bound
    {A : Type*} [AddCommGroup A] {ℓ B : ℕ}
    (hfin : (AddCommGroup.torsion A : Set A).Finite)
    (hbound : (AddCommGroup.torsion A : Set A).ncard ≤ B)
    (hB : B < 4 * ℓ) :
    ¬ ∃ f : ((ZMod 2 × ZMod 2) × ZMod ℓ) →+ A,
      Function.Injective f := by
  rintro ⟨f, hf⟩
  let : NeZero ℓ := ⟨by omega⟩
  let α := (ZMod 2 × ZMod 2) × ZMod ℓ
  have himage : f '' (Set.univ : Set α) ⊆ (AddCommGroup.torsion A : Set A) := by
    rintro y ⟨x, _, rfl⟩
    exact f.isOfFinAddOrder (isOfFinAddOrder_of_finite x)
  have hlow : Nat.card α ≤ (AddCommGroup.torsion A : Set A).ncard := by
    rw [← Set.ncard_univ, ← Set.ncard_image_of_injective _ hf]
    exact Set.ncard_le_ncard himage hfin
  have hα : Nat.card α = 4 * ℓ := by simp [α]
  rw [hα] at hlow
  omega
