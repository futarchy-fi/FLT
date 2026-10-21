/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInputNonsingular
public import FLT.Mazur.WeierstrassDividedTangentNonsingularInputs
public import FLT.Mazur.WeierstrassDividedSuppliedSmoothTangentDomain

/-!
# Actual smooth tangent coverage for punctured zero-depth self-pairs

Two punctured zero-depth inputs with nonzero tangent denominators have a
constructed smooth output in every supplied finite model. The input ring
may be nonreduced and no branch or output nonvanishing premise is imposed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [CommRing S] [Algebra R S] {W : WeierstrassCurve R} {π : R} {m : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π 0)
  (a c : Coordinate W (π ^ 0) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "T" => DividedTangentRing W (π ^ 0) d.b3 d.b4 d.b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "x₁" => a (x W (π ^ 0) d.b3 d.b4 d.b6)
local notation "x₂" => c (x W (π ^ 0) d.b3 d.b4 d.b6)
local notation "den" => dividedTangentDenominator W (π ^ 0) d.b3 d.b4 d.b6 a c
local notation "V" => suppliedSmoothTangentSmoothOpen d a c
local notation "f" => dividedTangentToCurve W (π ^ 0) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

include D

/-- The actual tangent output is smooth at every punctured zero-depth closed-fiber input. -/
theorem suppliedSmoothTangentSmoothOpen_zero_mem (hm : 0 < m) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal)
    (hx : (j) x₁ ∉ p.asIdeal) (hu : (j) x₂ ∉ p.asIdeal) : p ∈ V := by
  let ρ : T →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R T _
  have hπ : algebraMap R p.asIdeal.ResidueField π = 0 := by
    rw [IsScalarTower.algebraMap_apply R T p.asIdeal.ResidueField]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hp
  have h₁ := zeroDepthInput_nonsingular D d ((ρ.comp j).comp a) hm hπ
    (fun h => hx (Ideal.algebraMap_residueField_eq_zero.mp h))
  have h₂ := zeroDepthInput_nonsingular D d ((ρ.comp j).comp c) hm hπ
    (fun h => hu (Ideal.algebraMap_residueField_eq_zero.mp h))
  have hr := dividedTangentRefinement_range_smooth W (π ^ 0) d.b3 d.b4 d.b6 a c
    d.factor3 d.factor4 d.factor6 ρ (by simp only [pow_zero, map_one, ne_eq, one_ne_zero,
      not_false_eq_true]) h₁ h₂
  have he : Spec.map (CommRingCat.ofHom ρ.toRingHom) ⟨⊥, inferInstance⟩ = p := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro z
    change algebraMap T p.asIdeal.ResidueField z = 0 ↔ z ∈ p.asIdeal
    exact Ideal.algebraMap_residueField_eq_zero
  exact hr ⟨⟨⊥, inferInstance⟩, by rw [Scheme.Hom.comp_apply, he]⟩

/-- Punctured inputs with nonzero tangent denominator lie in the actual smooth tangent domain. -/
theorem suppliedSmoothTangentDomain_zero_mem (hm : 0 < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hx : x₁ ∉ p.asIdeal) (hu : x₂ ∉ p.asIdeal)
    (hd : den ∉ p.asIdeal) : p ∈ suppliedSmoothTangentDomain d a c := by
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T den).ge hd
  have memq (z : S) : algebraMap S T z ∈ q.asIdeal ↔ z ∈ p.asIdeal := by
    change z ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal ↔ z ∈ p.asIdeal
    rw [hq]
  have hpq : algebraMap R T π ∈ q.asIdeal := by
    rw [IsScalarTower.algebraMap_apply R S T]
    exact (memq _).mpr hp
  refine ⟨⟨q, suppliedSmoothTangentSmoothOpen_zero_mem D d a c hm q hpq
    ((memq _).not.mpr hx) ((memq _).not.mpr hu)⟩, ?_⟩
  exact hq

end FLT.Mazur.WeierstrassDividedDepth
