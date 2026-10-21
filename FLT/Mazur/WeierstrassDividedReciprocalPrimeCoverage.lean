/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalSmoothDomain
public import FLT.Mazur.WeierstrassDividedReciprocalSpecialization
public import FLT.Mazur.WeierstrassSmoothZeroSection
public import FLT.Mazur.WeierstrassDividedTangentSource
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Reciprocal coverage at equal residue abscissae

Equality is needed only in the residue field of the input point. The output
ordinate is then nonzero and the actual output is the smooth infinity point.
Thus the constructed open contains every such prime with nonzero ordinate
difference, without any smoothness assumption on the contracted inputs.
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
local notation "T" => DividedReciprocalRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "B" => DividedReciprocalOutputRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "v" => dividedReciprocalCoordinates W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "dx" => a (x W (π ^ k) d.b3 d.b4 d.b6) - c (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "dy" => a (y W (π ^ k) d.b3 d.b4 d.b6) - c (y W (π ^ k) d.b3 d.b4 d.b6)
local notation "out" => dividedReciprocalToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- Coincident residue abscissae make the homogeneous output ordinate nonzero. -/
theorem suppliedReciprocal_ordinate_not_mem (p : PrimeSpectrum T)
    (hx : algebraMap S T dx ∈ p.asIdeal) : v 1 ∉ p.asIdeal := by
  let e : T →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R T _
  have he : e (algebraMap S T (a (x W (π ^ k) d.b3 d.b4 d.b6))) =
      e (algebraMap S T (c (x W (π ^ k) d.b3 d.b4 d.b6))) := by
    apply sub_eq_zero.mp
    simpa only [e, IsScalarTower.coe_toAlgHom', map_sub] using
      Ideal.algebraMap_residueField_eq_zero.mpr hx
  have hv : e (v 1) = -1 :=
    dividedReciprocalSpecialization_coordinates W (π ^ k) d.b3 d.b4 d.b6 a c e he 1
  intro h
  have hz := Ideal.algebraMap_residueField_eq_zero.mpr h
  change e (v 1) = 0 at hz
  rw [hv] at hz
  exact neg_ne_zero.mpr one_ne_zero hz

/-- The normalized output is smooth whenever its residue abscissae coincide. -/
theorem suppliedReciprocalSmoothOpen_mem (p : PrimeSpectrum B)
    (hx : algebraMap T B (algebraMap S T dx) ∈ p.asIdeal) :
    p ∈ suppliedReciprocalSmoothOpen d a c := by
  let e : B →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R B _
  have he : e (algebraMap T B (algebraMap S T (a (x W (π ^ k) d.b3 d.b4 d.b6)))) =
      e (algebraMap T B (algebraMap S T (c (x W (π ^ k) d.b3 d.b4 d.b6)))) := by
    apply sub_eq_zero.mp
    simpa only [e, IsScalarTower.coe_toAlgHom', map_sub] using
      Ideal.algebraMap_residueField_eq_zero.mpr hx
  have ho := dividedReciprocalSpecialization_toCurve W (π ^ k) d.b3 d.b4 d.b6 a c
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

/-- Every equal-abscissa prime with nonzero ordinate difference has an actual smooth output. -/
theorem suppliedReciprocalDomain_mem (p : PrimeSpectrum S)
    (hx : dx ∈ p.asIdeal) (hy : dy ∉ p.asIdeal) :
    p ∈ suppliedReciprocalDomain d a c := by
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T dy).ge hy
  have hxq : algebraMap S T dx ∈ q.asIdeal := by
    change dx ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
    rwa [hq]
  obtain ⟨z, hz⟩ := (PrimeSpectrum.localization_away_comap_range B (v 1)).ge
    (suppliedReciprocal_ordinate_not_mem d a c q hxq)
  have hxz : algebraMap T B (algebraMap S T dx) ∈ z.asIdeal := by
    change algebraMap S T dx ∈ (PrimeSpectrum.comap (algebraMap T B) z).asIdeal
    rwa [hz]
  refine ⟨⟨z, suppliedReciprocalSmoothOpen_mem d a c z hxz⟩, ?_⟩
  change PrimeSpectrum.comap (algebraMap S T)
    (PrimeSpectrum.comap (algebraMap T B) z) = p
  rw [hz, hq]

/-- Outside both original slope opens, one nonzero vertical derivative suffices. -/
theorem suppliedReciprocalDomain_mem_of_denominators (p : PrimeSpectrum S)
    (hx : dx ∈ p.asIdeal)
    (he : dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a c ∈ p.asIdeal)
    (ha : a (verticalDerivative W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal) :
    p ∈ suppliedReciprocalDomain d a c := by
  apply suppliedReciprocalDomain_mem d a c p hx
  intro hy
  apply ha
  have h := p.asIdeal.add_mem (p.asIdeal.add_mem he hy)
    (p.asIdeal.mul_mem_left (algebraMap R S W.a₁) hx)
  convert h using 1
  simp only [verticalDerivative_eq, map_add, map_mul, map_ofNat, AlgHom.commutes,
    dividedTangentDenominator]
  ring

end FLT.Mazur.WeierstrassDividedDepth
