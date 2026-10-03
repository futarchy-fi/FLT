/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalExpMultiplicative
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The local exponential group equivalence

The exponential identifies the additive ball v(x) < v(p) with exactly
the principal units v(u-1) < v(p). The unit subgroup is constructed as
the range of the proved exponential homomorphism and then characterized.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  (p : ℕ) [Fact p.Prime]

/-- The explicit additive convergence neighborhood. -/
def localExpDomain : AddSubgroup L :=
  ((dvrPrime S).valuation L).ltAddSubgroup
    (Units.mk0 _ (localExpRadius_pos S L p).ne')

variable [CharP (ResidueField S) p] [IsAdicComplete (maximalIdeal S) S]

/-- The exponential on its domain, bundled as a homomorphism into field units. -/
def localExpHom : Multiplicative (localExpDomain S L p) →* Lˣ where
  toFun x :=
    { val := adicLocalExp S L (Multiplicative.toAdd x).val
      inv := adicLocalExp S L (-(Multiplicative.toAdd x).val)
      val_inv := adicLocalExp_mul_neg S L p _ (Multiplicative.toAdd x).property
      inv_val := by
        rw [mul_comm]
        exact adicLocalExp_mul_neg S L p _ (Multiplicative.toAdd x).property }
  map_one' := Units.ext (adicLocalExp_zero S L)
  map_mul' x y := Units.ext
    (adicLocalExp_add S L p _ _ (Multiplicative.toAdd x).property
      (Multiplicative.toAdd y).property)

/-- Logarithm proves injectivity of the constructed exponential homomorphism. -/
theorem localExpHom_injective : Function.Injective (localExpHom S L p) := by
  intro x y h
  have hv := congrArg (fun u : Lˣ => adicLocalLog S L (u : L)) h
  change adicLocalLog S L (adicLocalExp S L (Multiplicative.toAdd x).val) =
    adicLocalLog S L (adicLocalExp S L (Multiplicative.toAdd y).val) at hv
  rw [adicLocalLog_exp S L p _ (Multiplicative.toAdd x).property,
    adicLocalLog_exp S L p _ (Multiplicative.toAdd y).property] at hv
  exact Subtype.ext hv

/-- The principal-unit neighborhood obtained from the local exponential. -/
def localExpUnits : Subgroup Lˣ := (localExpHom S L p).range

/-- Its range is precisely the stated principal-unit neighborhood. -/
theorem mem_localExpUnits_iff (u : Lˣ) :
    u ∈ localExpUnits S L p ↔
      (dvrPrime S).valuation L ((u : L) - 1) < (dvrPrime S).valuation L (p : L) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (adicLocalExp_sub_one_le S L p _ (Multiplicative.toAdd x).property).trans_lt
      (Multiplicative.toAdd x).property
  · intro hu
    have hl : (dvrPrime S).valuation L (adicLocalLog S L (u : L)) <
        (dvrPrime S).valuation L (p : L) := by
      simpa only [add_sub_cancel] using (adicLocalLog_le S L p _ hu).trans_lt hu
    refine ⟨Multiplicative.ofAdd ⟨adicLocalLog S L (u : L), hl⟩, Units.ext ?_⟩
    change adicLocalExp S L (adicLocalLog S L (u : L)) = (u : L)
    simpa only [add_sub_cancel] using adicLocalExp_log S L p ((u : L) - 1) hu

/-- The proved additive-to-multiplicative group comparison on the chosen neighborhoods. -/
def localExpEquiv : Multiplicative (localExpDomain S L p) ≃* localExpUnits S L p :=
  MonoidHom.ofInjective (localExpHom_injective S L p)

end LocalClassFieldTheory
