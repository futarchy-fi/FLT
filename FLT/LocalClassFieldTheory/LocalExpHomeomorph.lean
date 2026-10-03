/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalExpIsometry
public import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# The local exponential is a homeomorphism

Exact valuation preservation identifies the induced uniformity. The proved
group equivalence is consequently a homeomorphism of the actual adic
neighborhoods, with continuous inverse logarithm.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing Filter
open scoped Topology Uniformity WithZero

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

/-- On the additive convergence subgroup, exponential preserves the induced uniformity. -/
theorem localExp_isUniformInducing :
    letI := dvrAdicValued S L
    IsUniformInducing (fun x : localExpDomain S L p => adicLocalExp S L x.val) := by
  let := dvrAdicValued S L
  constructor
  apply ((Valued.hasBasis_uniformity L ℤᵐ⁰).comap
    (fun q : localExpDomain S L p × localExpDomain S L p =>
      (adicLocalExp S L q.1.val, adicLocalExp S L q.2.val))).eq_of_same_basis
  have hb := (Valued.hasBasis_uniformity L ℤᵐ⁰).comap
    (fun q : localExpDomain S L p × localExpDomain S L p => (q.1.val, q.2.val))
  convert hb using 1
  · rfl
  ext γ q
  change (Valued.v.restrict (adicLocalExp S L q.2.val - adicLocalExp S L q.1.val) < γ.val) ↔
    (Valued.v.restrict (q.2.val - q.1.val) < γ.val)
  rw [Valued.v.restrict_inj.mpr (adicLocalExp_sub_valuation S L p _ _ q.2.property q.1.property)]

/-- The local exponential group equivalence induces the actual neighborhood topologies. -/
theorem localExpEquiv_isInducing :
    letI := dvrAdicValued S L
    Topology.IsInducing (localExpEquiv S L p) := by
  let := dvrAdicValued S L
  have hi : Topology.IsInducing
      (fun u : localExpUnits S L p => ((u.val : Lˣ) : L)) :=
    Units.isEmbedding_val₀.isInducing.comp Topology.IsEmbedding.subtypeVal.isInducing
  apply hi.of_comp_iff.mp
  have he := (localExp_isUniformInducing S L p).isInducing
  have hto : Topology.IsInducing (Multiplicative.toAdd :
      Multiplicative (localExpDomain S L p) → localExpDomain S L p) :=
    (show Multiplicative (localExpDomain S L p) ≃ₜ localExpDomain S L p from
      { toEquiv := Multiplicative.toAdd
        continuous_toFun := continuous_toAdd
        continuous_invFun := continuous_ofAdd }).isInducing
  exact he.comp hto

/-- Exponential and logarithm give a homeomorphism on the explicit neighborhoods. -/
def localExpHomeomorph :
    letI := dvrAdicValued S L
    Multiplicative (localExpDomain S L p) ≃ₜ localExpUnits S L p := by
  let := dvrAdicValued S L
  exact (localExpEquiv S L p).toEquiv.toHomeomorphOfIsInducing
    (localExpEquiv_isInducing S L p)

end LocalClassFieldTheory
