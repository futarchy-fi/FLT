/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialBasisOpen
public import FLT.Mazur.HilbertChartClassification

/-!
# A principal cover with actual Hilbert chart parameters

The intrinsic polynomial basis open is the union of principal neighborhoods
where the extended quotient has the prescribed basis. Each such neighborhood
has a unique chart parameter recovering the actual extended ideal.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

attribute [local irreducible] tupleLinearMap

variable (R : Type*) [CommRing R] (I : Type*) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type*) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))

/-- Principal neighborhoods on which the actual extended ideal has the required basis. -/
def PolynomialBasisNeighborhoods := {r : S //
  ∃ b : Module.Basis (Fin d) (Localization.Away r)
    (MvPolynomial I (Localization.Away r) ⧸
      J.map (MvPolynomial.map (algebraMap S (Localization.Away r)))),
    ∀ i, polynomialBasisTuple R I d w (Localization.Away r)
      (J.map (MvPolynomial.map (algebraMap S (Localization.Away r)))) i = b i}

/-- The actual localized ambient ideal, equipped only with its prescribed-basis property. -/
def neighborhoodIdeal (r : PolynomialBasisNeighborhoods R I d w S J) :
    PrescribedBasisIdeals R I d w (Localization.Away r.val) :=
  ⟨J.map (MvPolynomial.map (algebraMap S (Localization.Away r.val))), r.property⟩

/-- Classification constructs the parameter on each principal neighborhood. -/
def neighborhoodClassifyingMap (r : PolynomialBasisNeighborhoods R I d w S J) :
    ChartRing R I d w →ₐ[R] Localization.Away r.val :=
  idealClassifyingMap R I d w _ (neighborhoodIdeal R I d w S J r)

/-- The parameter recovers the actual ideal after localization. -/
theorem neighborhoodClassifyingMap_ideal (r : PolynomialBasisNeighborhoods R I d w S J) :
    pointIdeal R I d w (neighborhoodClassifyingMap R I d w S J r) =
      J.map (MvPolynomial.map (algebraMap S (Localization.Away r.val))) :=
  congrArg Subtype.val (idealOfPoint_idealClassifyingMap R I d w _
    (neighborhoodIdeal R I d w S J r))

variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]

/-- Every principal neighborhood carrying the basis lies in the intrinsic open. -/
theorem neighborhood_basicOpen_le (r : PolynomialBasisNeighborhoods R I d w S J) :
    PrimeSpectrum.basicOpen r.val ≤ polynomialBasisOpen R I d w S J := by
  have hb := (polynomialBasisTuple_basis_iff R I d w S (Localization.Away r.val) J).mpr
    r.property
  have hm := (localized_tuple_basis_iff (.powers r.val) (Localization.Away r.val)
    (TensorProduct.mk S (Localization.Away r.val) (MvPolynomial I S ⧸ J) 1)
    (polynomialBasisTuple R I d w S J)).mp hb
  intro p hp
  change Function.Bijective
    (LocalizedModule.map p.asIdeal.primeCompl (tupleLinearMap (polynomialBasisTuple R I d w S J)))
  exact localizedMap_bijective_of_le (.powers r.val) p.asIdeal.primeCompl
    (Submonoid.powers_le.mpr hp) _ hm

/-- These neighborhoods cover every point of the intrinsic open. -/
theorem exists_polynomialBasisNeighborhood (p : PrimeSpectrum S)
    (hp : p ∈ polynomialBasisOpen R I d w S J) :
    ∃ r : PolynomialBasisNeighborhoods R I d w S J, p ∈ PrimeSpectrum.basicOpen r.val := by
  obtain ⟨r, hr, hb, _⟩ := exists_principal_basis_neighborhood
    (polynomialBasisTuple R I d w S J) p hp
  exact ⟨⟨r, (polynomialBasisTuple_basis_iff R I d w S (Localization.Away r) J).mp hb⟩, hr⟩

/-- Gluing the actual principal neighborhoods gives exactly the intrinsic basis open. -/
theorem polynomialBasisOpen_eq_iSup :
    polynomialBasisOpen R I d w S J =
      ⨆ r : PolynomialBasisNeighborhoods R I d w S J, PrimeSpectrum.basicOpen r.val := by
  apply le_antisymm
  · intro p hp
    obtain ⟨r, hr⟩ := exists_polynomialBasisNeighborhood R I d w S J p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨r, hr⟩
  · exact iSup_le (neighborhood_basicOpen_le R I d w S J)

end FLT.Mazur.HilbertChart
