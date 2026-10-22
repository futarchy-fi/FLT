/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedMiddleSecantResidue
public import FLT.Mazur.WeierstrassDividedSuppliedSmoothSecantDomain

/-!
# Smooth secant domains at exact middle depth

Every secant localization point on the closed fiber has a smooth original
output. Pulling this back to the full input source covers the entire secant
denominator open, including inputs with zero horizontal coordinate.
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
  [CommRing S] [Algebra R S] {W : WeierstrassCurve R} {π : R} {m k : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "T" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "x₁" => a (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "x₂" => c (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "den" => x₁ - x₂
local notation "V" => suppliedSmoothSecantSmoothOpen d a c
local notation "f" => dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

include D

/-- Every middle-depth secant localization point has a smooth original output. -/
theorem suppliedSmoothSecantSmoothOpen_middle_mem (hk : 0 < k) (hm : 2 * k = m)
    (p : PrimeSpectrum T) (hp : algebraMap R T π ∈ p.asIdeal) : p ∈ V := by
  let ρ : T →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R T _
  have hπ : algebraMap R p.asIdeal.ResidueField π = 0 := by
    rw [IsScalarTower.algebraMap_apply R T p.asIdeal.ResidueField]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hp
  have hx := (middleSecantOutput_x_isUnit D d a c ρ hk hm hπ).ne_zero
  have hr := dividedSecant_range_smooth_of_x W (π ^ k) d.b3 d.b4 d.b6 a c
    d.factor3 d.factor4 d.factor6 ρ
    (by rw [map_pow, hπ, zero_pow (by omega)]) hx
  have he : Spec.map (CommRingCat.ofHom ρ.toRingHom) ⟨⊥, inferInstance⟩ = p := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro z
    change algebraMap T p.asIdeal.ResidueField z = 0 ↔ z ∈ p.asIdeal
    exact Ideal.algebraMap_residueField_eq_zero
  exact hr ⟨⟨⊥, inferInstance⟩, by rw [Scheme.Hom.comp_apply, he]⟩

/-- Every middle-depth pair with nonzero secant denominator reaches the actual output domain. -/
theorem suppliedSmoothSecantDomain_middle_mem (hk : 0 < k) (hm : 2 * k = m)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hd : den ∉ p.asIdeal) : p ∈ suppliedSmoothSecantDomain d a c := by
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T den).ge hd
  have hpq : algebraMap R T π ∈ q.asIdeal := by
    rw [IsScalarTower.algebraMap_apply R S T]
    change algebraMap R S π ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
    rwa [hq]
  exact ⟨⟨q, suppliedSmoothSecantSmoothOpen_middle_mem D d a c hk hm q hpq⟩, hq⟩

end FLT.Mazur.WeierstrassDividedDepth
