/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientFullQuotient
public import FLT.Mazur.HilbertMonomialReindexedAmbient
public import FLT.Mazur.HilbertIntrinsicBasisGlobal

/-!
# The matching Grassmannian chart detects the original Hilbert basis

Selected columns in the ambient quotient are carried to the prescribed
monomials in the full polynomial quotient. Bijectivity is therefore exactly
the Hilbert basis condition, over the original coefficient algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R S I : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (J : Ideal (MvPolynomial I S)) (d : ℕ)
  [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)
  (m : Fin d → BoundedHilbertMonomials I d) (hm : Function.Injective m)
  {κ : Type u} [Fintype κ] (e : HilbertComplementMonomials I d m ≃ κ)
local notation "N" => finiteFlatHilbertAmbientPoint R S I J d hd
local notation "c" => hilbertReindexedAmbient R I d m hm e
local notation "y" => (fun j ↦ Ideal.Quotient.mk J (MvPolynomial.monomial (Subtype.val (m j)) 1))

/-- The selected column map becomes exactly the original monomial tuple map. -/
theorem hilbertAmbientFullQuotientEquiv_selected :
    (hilbertAmbientFullQuotientEquiv R S I J d hd).toLinearMap.comp
        ((N).toSubmodule.mkQ.comp (ambientChartSelected (ambientChartBaseChange S c))) =
      tupleLinearMap (R := S) y := by
  apply (Pi.basisFun S (Fin d)).ext
  intro j
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hilbertReindexedAmbient_selected]
  change hilbertAmbientFullQuotientEquiv R S I J d hd _ = _
  rw [hilbertAmbientFullQuotientEquiv_monomial]
  exact (Module.Basis.constr_basis (Pi.basisFun S (Fin d)) S y j).symm

/-- Membership in the matching ambient chart is equivalent to an actual monomial basis. -/
theorem hilbertMonomialChart_basis_iff :
    Function.Bijective
        ((N).toSubmodule.mkQ.comp (ambientChartSelected (ambientChartBaseChange S c))) ↔
      ∃ v : Module.Basis (Fin d) S (MvPolynomial I S ⧸ J), ∀ j, v j = y j := by
  rw [tuple_basis_iff_bijective, ← hilbertAmbientFullQuotientEquiv_selected R S I J d hd m hm e]
  exact (Function.Bijective.of_comp_iff'
    (hilbertAmbientFullQuotientEquiv R S I J d hd).bijective _).symm

end FLT.Mazur.HilbertChart
