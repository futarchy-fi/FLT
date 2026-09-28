/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HeightOneStructure
public import FLT.GroupScheme.HopfFrobenius
public import FLT.Mathlib.RingTheory.CotangentQuotient

/-!
# The truncated polynomial structure of the Frobenius kernel

For every finite local commutative Hopf algebra in characteristic `p`, its
quotient by the Frobenius powers of the augmentation ideal is a truncated
polynomial algebra. No height-one assumption on the original Hopf algebra is
made: the quotient automatically satisfies that assumption.
-/

@[expose] public noncomputable section

namespace AlgHom

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
variable (p : ℕ) [Fact p.Prime] [CharP A p]

/-- Taking the Frobenius augmentation quotient preserves the cotangent dimension. -/
theorem finrank_cotangent_frobeniusQuotient (ε : A →ₐ[k] k) :
    Module.finrank k (RingHom.ker (ε.frobeniusQuotientAugmentation p)).Cotangent =
      Module.finrank k (RingHom.ker ε).Cotangent := by
  have hker : RingHom.ker (ε.frobeniusQuotientAugmentation p) =
      (RingHom.ker ε).map (Ideal.Quotient.mk ((RingHom.ker ε).frobeniusPower p)) :=
    Ideal.ker_quotient_lift ε.toRingHom _
  rw [hker]
  exact Ideal.finrank_cotangent_map_quotient k _ _ ((RingHom.ker ε).frobeniusPower_le_sq p)

end AlgHom

namespace HopfAlgebra

variable {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
  [Module.Finite k A] [IsLocalRing A]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]

/-- The coordinate algebra of the Frobenius kernel is a truncated polynomial algebra. -/
theorem nonempty_frobeniusKernel_algEquiv :
    let ε := Bialgebra.counitAlgHom k A
    let I := (RingHom.ker ε).frobeniusPower p
    let n := Module.finrank k (RingHom.ker (ε.frobeniusQuotientAugmentation p)).Cotangent
    Nonempty ((MvPolynomial (Fin n) k ⧸
      Ideal.span (Set.range (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) k) ^ p))) ≃ₐ[k]
        (A ⧸ I)) := by
  let ε := Bialgebra.counitAlgHom k A
  let I := (RingHom.ker ε).frobeniusPower p
  let : I.IsHopfIdeal k := isHopfIdeal_frobeniusPower_augmentation p
  let : Nontrivial (A ⧸ I) := (ε.frobeniusQuotientAugmentation p).domain_nontrivial
  let : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact Bialgebra.nonempty_heightOne_algEquiv p
    (fun a ha ↦ ε.pow_eq_zero_on_ker_frobeniusQuotient p a ha)

/-- The Frobenius kernel uses the cotangent dimension of the original Hopf algebra. -/
theorem nonempty_frobeniusKernel_algEquiv_minimal :
    let ε := Bialgebra.counitAlgHom k A
    let n := Module.finrank k (RingHom.ker ε).Cotangent
    Nonempty ((MvPolynomial (Fin n) k ⧸
      Ideal.span (Set.range (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) k) ^ p))) ≃ₐ[k]
        (A ⧸ (RingHom.ker ε).frobeniusPower p)) := by
  have h := nonempty_frobeniusKernel_algEquiv (k := k) (A := A) p
  dsimp only at h ⊢
  rw [AlgHom.finrank_cotangent_frobeniusQuotient] at h
  exact h

end HopfAlgebra
