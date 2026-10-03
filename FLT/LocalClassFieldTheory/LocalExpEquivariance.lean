/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicGaloisContinuity
public import FLT.LocalClassFieldTheory.LocalExpHomeomorph

/-!
# Galois equivariance of local exp and log

The proved continuity of the actual automorphisms lets them pass through
the convergent sums. Rational coefficients are fixed, so both analytic
maps and the principal-unit group comparison are equivariant.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S L : Type) [CommRing R] [CommRing S] [IsDomain S]
  [IsDiscreteValuationRing S] [Field L] [Algebra R L] [Algebra S L]
  [IsFractionRing S L] [IsIntegralClosure S R L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

omit [CharZero L] [IsAdicComplete (maximalIdeal S) S]
  [Fact p.Prime] [CharP (ResidueField S) p] in
/-- Galois automorphisms preserve the explicit exponential convergence ball. -/
theorem localExpDomain_galois (σ : L ≃ₐ[R] L) (x : L) :
    (dvrPrime S).valuation L (σ x) < (dvrPrime S).valuation L (p : L) ↔
      (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L) := by
  have h := Valuation.isEquiv_iff_val_lt_val.mp (adicGalois_valuation_isEquiv R S L σ)
    (x := x) (y := (p : L))
  change ((dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L) ↔
    (dvrPrime S).valuation L (σ x) < (dvrPrime S).valuation L (σ (p : L))) at h
  rw [map_natCast σ p] at h
  exact h.symm

/-- The actual exponential sum commutes with each local Galois automorphism. -/
theorem adicLocalExp_galois (σ : L ≃ₐ[R] L) (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    σ (adicLocalExp S L x) = adicLocalExp S L (σ x) := by
  let := dvrAdicValued S L
  have h := (adicLocalExp_summable S L p x hx).hasSum.map σ.toAddMonoidHom
    (adicGalois_continuous R S L σ)
  change HasSum (fun n : ℕ => σ (x ^ n / (n.factorial : L)))
    (σ (adicLocalExp S L x)) at h
  simpa only [map_div₀, map_pow, map_natCast, adicLocalExp] using h.tsum_eq.symm

/-- The actual logarithm sum commutes with each local Galois automorphism. -/
theorem adicLocalLog_galois (σ : L ≃ₐ[R] L) (u : L)
    (hu : (dvrPrime S).valuation L (u - 1) < (dvrPrime S).valuation L (p : L)) :
    σ (adicLocalLog S L u) = adicLocalLog S L (σ u) := by
  let := dvrAdicValued S L
  have h := (localLog_summable S L p (u - 1) hu).hasSum.map σ.toAddMonoidHom
    (adicGalois_continuous R S L σ)
  change HasSum (fun n => σ (localLogTerm (u - 1) n)) (σ (adicLocalLog S L u)) at h
  simpa only [localLogTerm, map_div₀, map_mul, map_pow, map_neg, map_one, map_natCast,
    map_sub, adicLocalLog] using h.tsum_eq.symm

/-- The additive domain carries the actual automorphism, with no action invariance assumed. -/
def localExpDomainGalois (σ : L ≃ₐ[R] L) : localExpDomain S L p ≃+ localExpDomain S L p where
  toFun x := ⟨σ x.val, (localExpDomain_galois R S L p σ x.val).mpr x.property⟩
  invFun x := ⟨σ.symm x.val, (localExpDomain_galois R S L p σ.symm x.val).mpr x.property⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x.val)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add σ x.val y.val)

/-- The bundled exponential into units intertwines the actual Galois actions. -/
theorem localExpHom_galois (σ : L ≃ₐ[R] L) (x : localExpDomain S L p) :
    localExpHom S L p (Multiplicative.ofAdd (localExpDomainGalois R S L p σ x)) =
      Units.map σ.toMonoidHom (localExpHom S L p (Multiplicative.ofAdd x)) := by
  apply Units.ext
  exact (adicLocalExp_galois R S L p σ x.val x.property).symm

end LocalClassFieldTheory
