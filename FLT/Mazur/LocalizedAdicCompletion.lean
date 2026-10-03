/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionQuotientEquiv
public import Mathlib.RingTheory.Localization.AtPrime.Basic
/-!
# Completion and localization at a maximal ideal

Localizing at a maximal ideal preserves every quotient by its powers.
The compatible quotient isomorphisms identify the completed algebras.
-/

open AdicCompletion
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LocalizedAdicCompletion
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
  (p : Ideal A) [p.IsMaximal] (L : Type*) [CommRing L] [Algebra A L]
  [IsLocalization.AtPrime L p] [IsLocalRing L] [Algebra K L] [IsScalarTower K A L]
/-- The quotient isomorphism for localization at a maximal ideal, retaining base scalars. -/
def quotient (n : ℕ) : (A ⧸ p ^ n) ≃ₐ[K] (L ⧸ IsLocalRing.maximalIdeal L ^ n) :=
  (IsLocalization.AtPrime.equivQuotMaximalIdealPow p L n).restrictScalars K
theorem compatible {m n : ℕ} (hmn : m ≤ n) (x : A ⧸ p ^ n) :
    Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn) (quotient (K := K) p L n x) =
      quotient (K := K) p L m (Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn) x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl
/-- Localization at a maximal ideal preserves the adic completion as a base algebra. -/
def equivalence : AdicCompletion p A ≃ₐ[K] AdicCompletion (IsLocalRing.maximalIdeal L) L :=
  AdicCompletionQuotientEquiv.equivalence p _ (quotient (K := K) p L) (compatible (K := K) p L)
end FLT.Mazur.LocalizedAdicCompletion
