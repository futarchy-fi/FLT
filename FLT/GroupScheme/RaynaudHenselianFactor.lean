/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.HenselianLocalRing.Finite
public import FLT.GroupScheme.RaynaudUnramifiedStage
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Henselian factors through prescribed roots

The minimal polynomial of a prescribed integral root gives the required factor.
Finite domains over a Henselian local ring are local; separability of the special
fibre then makes the reduced minimal polynomial irreducible.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace RaynaudParameters

/-- A finite domain over a Henselian local ring is local. -/
theorem isLocalRing_of_finite_domain (R A : Type*) [CommRing R] [HenselianLocalRing R]
    [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A] : IsLocalRing A := by
  obtain ⟨n, e, he, hlocal⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing (R := R) (A := A)
  have hex : ∃ i, e i ≠ 0 := by
    by_contra! h
    have := he.complete
    simp [h] at this
  obtain ⟨i, hi⟩ := hex
  have he1 : e i = 1 := (IsIdempotentElem.iff_eq_zero_or_one.mp (he.idem i)).resolve_left hi
  let f := algebraMap A (he.idem i).Corner
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg Subtype.val h
    change x * e i = y * e i at hh
    simpa [he1] using hh
  let := hlocal i
  exact (RingEquiv.ofBijective f ⟨hf, (he.idem i).toCorner_surjective⟩).symm.isLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R]

/-- An irreducible monic polynomial with separable reduction has irreducible reduction. -/
theorem irreducible_map_residue_of_henselian {P : R[X]} (hm : P.Monic)
    (hi : Irreducible P) (hs : (P.map (residue R)).Separable) :
    Irreducible (P.map (residue R)) := by
  let : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime hi.prime
  let := hm.finite_adjoinRoot
  let := isLocalRing_of_finite_domain R (AdjoinRoot P)
  let p := P.map (residue R)
  have hpdeg : p.degree ≠ 0 := by
    rw [hm.degree_map]
    intro h
    exact hi.not_isUnit (hm.isUnit_iff.mpr (hm.degree_le_zero_iff_eq_one.mp h.le))
  let := AdjoinRoot.nontrivial p hpdeg
  let f := AdjoinRoot.map (residue R) P p (dvd_refl p)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
    obtain ⟨q, rfl⟩ := Polynomial.map_surjective _ residue_surjective q
    exact ⟨AdjoinRoot.mk P q, RingHom.congr_fun (AdjoinRoot.map_comp_mk (residue R) (p := P) rfl) q⟩
  let : IsLocalRing (AdjoinRoot p) := IsLocalRing.of_surjective' f hf
  have hrad : (Ideal.span {p}).IsRadical := isRadical_iff_span_singleton.mp hs.squarefree.isRadical
  let : IsReduced (AdjoinRoot p) := (Ideal.isRadical_iff_quotient_reduced _).mp hrad
  let := (hm.map (residue R)).finite_adjoinRoot
  let : IsArtinianRing (AdjoinRoot p) := .of_finite (ResidueField R) _
  exact AdjoinRoot.isField_iff_irreducible.mp
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing (AdjoinRoot p))

/-- Choose the monic factor containing a prescribed root in the common overfield. -/
theorem exists_monic_factor_prescribed_root {Ω : Type*} [Field Ω] [Algebra R Ω]
    [FaithfulSMul R Ω] {P : R[X]} (hm : P.Monic)
    (hs : (P.map (residue R)).Separable) (x : Ω) (hx : aeval x P = 0) :
    ∃ Q : R[X], Q.Monic ∧ Q ∣ P ∧ Irreducible (Q.map (residue R)) ∧
      (Q.map (residue R)).Separable ∧ aeval x Q = 0 := by
  have hint : IsIntegral R x := ⟨P, hm, hx⟩
  have hd := minpoly.isIntegrallyClosed_dvd hint hx
  have hsep := hs.of_dvd (Polynomial.map_dvd (residue R) hd)
  exact ⟨minpoly R x, minpoly.monic hint, hd,
    irreducible_map_residue_of_henselian (minpoly.monic hint) (minpoly.irreducible hint) hsep,
    hsep, minpoly.aeval R x⟩

end RaynaudParameters
