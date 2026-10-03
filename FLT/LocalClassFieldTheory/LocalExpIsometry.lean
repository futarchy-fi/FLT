/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalExpEquivalence

/-!
# Exact valuation preservation by the local exponential

The bounds on exp and log, together with their inverse identities, force
v(exp(x)-1)=v(x). Multiplicativity then gives exact preservation of differences.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing IsDedekindDomain

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

omit [CharZero L] [IsAdicComplete (maximalIdeal S) S]
  [Fact p.Prime] [CharP (ResidueField S) p] in
/-- The chosen convergence radius is at most one. -/
theorem localExpRadius_le_one : (dvrPrime S).valuation L (p : L) ≤ 1 := by
  rw [← map_natCast (algebraMap S L)]
  exact HeightOneSpectrum.valuation_le_one (dvrPrime S) (p : S)

/-- The exponential has valuation one throughout its convergence ball. -/
theorem adicLocalExp_valuation (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    (dvrPrime S).valuation L (adicLocalExp S L x) = 1 := by
  have h := ((adicLocalExp_sub_one_le S L p x hx).trans_lt hx).trans_le
    (localExpRadius_le_one S L p)
  simpa only [map_one] using ((dvrPrime S).valuation L).map_eq_of_sub_lt (x := 1)
    (by simpa only [map_one] using h)

/-- The exponential displacement has exactly the input's valuation. -/
theorem adicLocalExp_sub_one_valuation (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    (dvrPrime S).valuation L (adicLocalExp S L x - 1) = (dvrPrime S).valuation L x := by
  apply le_antisymm (adicLocalExp_sub_one_le S L p x hx)
  have h := adicLocalLog_le S L p (adicLocalExp S L x - 1)
    ((adicLocalExp_sub_one_le S L p x hx).trans_lt hx)
  simpa only [add_sub_cancel, adicLocalLog_exp S L p x hx] using h

/-- The exponential preserves valuations of differences on its domain. -/
theorem adicLocalExp_sub_valuation (x y : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L))
    (hy : (dvrPrime S).valuation L y < (dvrPrime S).valuation L (p : L)) :
    (dvrPrime S).valuation L (adicLocalExp S L x - adicLocalExp S L y) =
      (dvrPrime S).valuation L (x - y) := by
  have hxy := ((dvrPrime S).valuation L).map_sub_lt hx hy
  have he : adicLocalExp S L (x - y) * adicLocalExp S L y = adicLocalExp S L x := by
    rw [← adicLocalExp_add S L p _ _ hxy hy, sub_add_cancel]
  have hd : adicLocalExp S L x - adicLocalExp S L y =
      (adicLocalExp S L (x - y) - 1) * adicLocalExp S L y := by
    rw [sub_mul, one_mul, he]
  rw [hd, map_mul, adicLocalExp_valuation S L p y hy, mul_one,
    adicLocalExp_sub_one_valuation S L p _ hxy]

end LocalClassFieldTheory
