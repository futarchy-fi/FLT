/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealCoordinates
public import FLT.Mazur.FiniteLocallyFreeDegreeAffine
public import FLT.Mazur.HilbertPolynomialAffineClassification

/-!
# Actual coordinate quotients of finite flat polynomial ideal families

Finite locally free degree of an ideal sheaf's closed projection implies
finite presentation, flatness and residue rank of its full coordinate
quotient. No basis or affine presentation of the ideal sheaf is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] coordinateIdeal

variable (I S : Type u) [CommRing S] (d : ℕ)
variable (J : (Spec (.of (MvPolynomial I S))).IdealSheafData)
variable (hJ : FiniteLocallyFreeDegree (J.subschemeι ≫
  Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I)))) d)
include hJ

/-- The full coordinate quotient has the degree of the actual closed ideal family. -/
theorem polynomialCoordinateIdeal_degree :
    FiniteLocallyFreeDegree (Spec.map (CommRingCat.ofHom
      (algebraMap S (MvPolynomial I S ⧸ coordinateIdeal (.of (MvPolynomial I S)) J)))) d := by
  let K := coordinateIdeal (.of (MvPolynomial I S)) J
  let q := Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I)))
  have hp : FiniteLocallyFreeDegree
      ((baseIdeal (.of (MvPolynomial I S)) K).subschemeι ≫ q) d := by
    change FiniteLocallyFreeDegree
      ((baseIdeal _ (coordinateIdeal _ J)).subschemeι ≫ q) d
    rw [baseIdeal_coordinateIdeal]
    exact hJ
  let E : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap S (MvPolynomial I S ⧸ K)))) ≅
      Over.mk ((baseIdeal (.of (MvPolynomial I S)) K).subschemeι ≫ q) := by
    refine Over.isoMk (quotientSpecIso (.of (MvPolynomial I S)) K) ?_
    change (quotientSpecIso (.of (MvPolynomial I S)) K).hom ≫
      (baseIdeal (.of (MvPolynomial I S)) K).subschemeι ≫ q = _
    rw [← Category.assoc, quotientSpecIso_hom_ι, ← Spec.map_comp]
    rfl
  exact (finiteLocallyFreeDegree_iff_of_overIso E).mpr hp

/-- The coordinate quotient is finitely presented as a module over its coefficients. -/
theorem polynomialCoordinateIdeal_finitePresentation :
    Module.FinitePresentation S
      (MvPolynomial I S ⧸ coordinateIdeal (.of (MvPolynomial I S)) J) :=
  finiteLocallyFreeDegree_moduleFinitePresentation S _ d
    (polynomialCoordinateIdeal_degree I S d J hJ)

/-- The coordinate quotient is flat over the original coefficient ring. -/
theorem polynomialCoordinateIdeal_flat :
    Module.Flat S (MvPolynomial I S ⧸ coordinateIdeal (.of (MvPolynomial I S)) J) :=
  finiteLocallyFreeDegree_moduleFlat S _ d (polynomialCoordinateIdeal_degree I S d J hJ)

/-- Every actual residue quotient has the degree of the original closed family. -/
theorem polynomialCoordinateIdeal_residueRank (p : PrimeSpectrum S) :
    Module.finrank p.asIdeal.ResidueField (MvPolynomial I p.asIdeal.ResidueField ⧸
      (coordinateIdeal (.of (MvPolynomial I S)) J).map
        (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d := by
  rw [← (polynomialQuotientBaseChangeEquiv I S p.asIdeal.ResidueField
    (coordinateIdeal (.of (MvPolynomial I S)) J)).toLinearEquiv.finrank_eq]
  exact finiteLocallyFreeDegree_residueFinrank S _ d
    (polynomialCoordinateIdeal_degree I S d J hJ) p

/-- The full coordinate ideal defines an actual family in affine Hilbert classification. -/
def polynomialCoordinateFamily : PolynomialQuotientFamilies I d S :=
  ⟨coordinateIdeal (.of (MvPolynomial I S)) J,
    polynomialCoordinateIdeal_finitePresentation I S d J hJ,
    polynomialCoordinateIdeal_flat I S d J hJ,
    polynomialCoordinateIdeal_residueRank I S d J hJ⟩

end FLT.Mazur.HilbertChart
