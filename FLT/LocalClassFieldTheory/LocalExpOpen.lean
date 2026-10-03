/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalExpHomeomorph

/-!
# Openness of local exponential images

The explicitly characterized principal-unit neighborhood is open. Together
with the proved homeomorphism, this makes exponentiation an open map into
all field units, which applies to smaller open lattices.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing
open scoped WithZero

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

/-- The actual principal-unit subgroup in the exponential range is open. -/
theorem localExpUnits_isOpen :
    letI := dvrAdicValued S L
    IsOpen (localExpUnits S L p : Set Lˣ) := by
  let := dvrAdicValued S L
  convert (Valued.isOpen_ball L (Valued.v.restrict (p : L))).preimage
    (Units.continuous_val.sub continuous_const) using 1
  · ext u
    exact (mem_localExpUnits_iff S L p u).trans Valued.v.restrict_lt_iff.symm

/-- Exponentiation on the convergence subgroup is open into the field unit group. -/
theorem localExpHom_isOpenMap :
    letI := dvrAdicValued S L
    IsOpenMap (localExpHom S L p) := by
  let := dvrAdicValued S L
  exact (localExpUnits_isOpen S L p).isOpenMap_subtype_val.comp
    (localExpHomeomorph S L p).isOpenMap

end LocalClassFieldTheory
