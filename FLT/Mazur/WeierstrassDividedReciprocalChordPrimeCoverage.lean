/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalChordSmoothDomain
public import FLT.Mazur.WeierstrassDividedReciprocalChordSpecialization
public import FLT.Mazur.WeierstrassSmoothZeroSection
public import FLT.Mazur.WeierstrassDividedTangentSource

/-!
# Reciprocal chord coverage at vanishing tangent denominators

Vanishing is required only in the input residue field. The full constructed
output specializes to infinity, including in characteristic two with equal
inputs and zero abscissae. No ordinate difference is inverted.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (d : Data W π k)
  (a c : WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "T" => DividedReciprocalChordRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "B" => DividedReciprocalChordOutputRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "v" => dividedReciprocalChordCoordinates W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "dx" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "dy" => dividedTangentNumerator W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "out" => dividedReciprocalChordToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- Zero residue tangent denominators make the homogeneous output ordinate nonzero. -/
theorem suppliedReciprocalChord_ordinate_not_mem (p : PrimeSpectrum T)
    (hx : algebraMap S T dx ∈ p.asIdeal) : v 1 ∉ p.asIdeal := by
  let e : T →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R T _
  have he : e (algebraMap S T dx) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hx
  have hv : e (v 1) = -1 :=
    dividedReciprocalChordSpecialization_coordinates W (π ^ k) d.b3 d.b4 d.b6 a c e he 1
  intro h
  have hz := Ideal.algebraMap_residueField_eq_zero.mpr h
  change e (v 1) = 0 at hz
  rw [hv] at hz
  exact neg_ne_zero.mpr one_ne_zero hz

/-- The normalized output is smooth whenever its residue tangent denominator vanishes. -/
theorem suppliedReciprocalChordSmoothOpen_mem (p : PrimeSpectrum B)
    (hx : algebraMap T B (algebraMap S T dx) ∈ p.asIdeal) :
    p ∈ suppliedReciprocalChordSmoothOpen d a c := by
  let e : B →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R B _
  have he : e (algebraMap T B (algebraMap S T dx)) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hx
  have ho := dividedReciprocalChordSpecialization_toCurve W (π ^ k) d.b3 d.b4 d.b6 a c
    d.factor3 d.factor4 d.factor6 e he
  obtain ⟨q, hq⟩ := (PrimeSpectrum.residueField_comap p).symm ▸
    (Set.mem_singleton p : p ∈ ({p} : Set (PrimeSpectrum B)))
  change out p ∈ integralSmoothOpen W
  have h := congrArg (fun f => f q) ho
  simp only [Scheme.Hom.comp_apply] at h
  change out (PrimeSpectrum.comap (algebraMap B p.asIdeal.ResidueField) q) = _ at h
  rw [hq] at h
  rw [h]
  exact integralCurveZero_range_smooth W ⟨_, rfl⟩

/-- Every zero-denominator prime with nonzero chord numerator has an actual smooth output. -/
theorem suppliedReciprocalChordDomain_mem (p : PrimeSpectrum S)
    (hx : dx ∈ p.asIdeal) (hy : dy ∉ p.asIdeal) :
    p ∈ suppliedReciprocalChordDomain d a c := by
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T dy).ge hy
  have hxq : algebraMap S T dx ∈ q.asIdeal := by
    change dx ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
    rwa [hq]
  obtain ⟨z, hz⟩ := (PrimeSpectrum.localization_away_comap_range B (v 1)).ge
    (suppliedReciprocalChord_ordinate_not_mem d a c q hxq)
  have hxz : algebraMap T B (algebraMap S T dx) ∈ z.asIdeal := by
    change algebraMap S T dx ∈ (PrimeSpectrum.comap (algebraMap T B) z).asIdeal
    rwa [hz]
  refine ⟨⟨z, suppliedReciprocalChordSmoothOpen_mem d a c z hxz⟩, ?_⟩
  change PrimeSpectrum.comap (algebraMap S T)
    (PrimeSpectrum.comap (algebraMap T B) z) = p
  rw [hz, hq]

end FLT.Mazur.WeierstrassDividedDepth
