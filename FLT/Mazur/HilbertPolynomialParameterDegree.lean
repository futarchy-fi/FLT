/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocallyFreeDegreeAffine
public import FLT.Mazur.HilbertPolynomialParameterClosedPullback

/-!
# Finite flat polynomial quotients of arbitrary Hilbert parameters

The actual pulled-back coordinate ideal gives a finitely presented flat
quotient of constant residue rank. All properties follow from the universal
projection and the proved cartesian comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d =
  Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The coordinate quotient of an arbitrary parameter has finite locally free degree `d`. -/
theorem polynomialParameterIdeal_degree :
    FiniteLocallyFreeDegree (Spec.map (CommRingCat.ofHom (algebraMap S
      (MvPolynomial I S ⧸ polynomialParameterIdeal R I d S f hf)))) d := by
  let J := polynomialParameterIdeal R I d S f hf
  let p := (baseIdeal (.of (MvPolynomial I S)) J).subschemeι ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I)))
  have hp : FiniteLocallyFreeDegree p d :=
    finiteLocallyFreeDegree_of_isPullback (polynomialParameterClosedMap_isPullback R I d S f hf)
      d (polynomialUniversalProjection_degree R I d)
  let e : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap S (MvPolynomial I S ⧸ J)))) ≅ Over.mk p := by
    refine Over.isoMk (quotientSpecIso (.of (MvPolynomial I S)) J) ?_
    change (quotientSpecIso (.of (MvPolynomial I S)) J).hom ≫
      (baseIdeal (.of (MvPolynomial I S)) J).subschemeι ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I))) =
      Spec.map (CommRingCat.ofHom (algebraMap S (MvPolynomial I S ⧸ J)))
    rw [← Category.assoc, quotientSpecIso_hom_ι, ← Spec.map_comp]
    rfl
  exact (finiteLocallyFreeDegree_iff_of_overIso e).mpr hp

/-- The actual parameter quotient is finite as a module over its coefficient ring. -/
instance polynomialParameterIdeal_finite :
    Module.Finite S (MvPolynomial I S ⧸ polynomialParameterIdeal R I d S f hf) :=
  finiteLocallyFreeDegree_moduleFinite S _ d (polynomialParameterIdeal_degree R I d S f hf)

/-- The actual parameter quotient is flat over its coefficient ring. -/
instance polynomialParameterIdeal_flat :
    Module.Flat S (MvPolynomial I S ⧸ polynomialParameterIdeal R I d S f hf) :=
  finiteLocallyFreeDegree_moduleFlat S _ d (polynomialParameterIdeal_degree R I d S f hf)

/-- The actual parameter quotient is finitely presented as a module. -/
instance polynomialParameterIdeal_finitePresentation :
    Module.FinitePresentation S (MvPolynomial I S ⧸ polynomialParameterIdeal R I d S f hf) :=
  finiteLocallyFreeDegree_moduleFinitePresentation S _ d
    (polynomialParameterIdeal_degree R I d S f hf)

/-- Every residue quotient has exactly the prescribed dimension. -/
theorem polynomialParameterIdeal_residueRank (p : PrimeSpectrum S) :
    Module.finrank p.asIdeal.ResidueField (MvPolynomial I p.asIdeal.ResidueField ⧸
      (polynomialParameterIdeal R I d S f hf).map
        (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d := by
  rw [← (polynomialQuotientBaseChangeEquiv I S p.asIdeal.ResidueField
    (polynomialParameterIdeal R I d S f hf)).toLinearEquiv.finrank_eq]
  exact finiteLocallyFreeDegree_residueFinrank S _ d
    (polynomialParameterIdeal_degree R I d S f hf) p

end FLT.Mazur.HilbertChart
