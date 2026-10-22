/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentNonsingularInputs
public import FLT.Mazur.EllipticNormalizedSingularity
public import FLT.Mazur.WeierstrassProjectivePointSmooth

/-!
# Smooth tangent outputs over arbitrary source primes

A nonzero output abscissa on a nodal fiber gives an actual relatively
smooth output. The criterion uses the source prime's residue field and
therefore applies to arbitrary source rings, including nonreduced ones.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "out" => dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6
local notation "f" => dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6

/-- On a nodal fiber a nonzero output abscissa certifies nonsingularity. -/
theorem dividedTangent_nonsingular_of_x {K : Type u} [Field K] [Algebra R K]
    (e : T →ₐ[R] K) (hs : algebraMap R K s = 0)
    (hx : e (dividedTangentX W s b3 b4 b6 a c) ≠ 0) :
    (W.map (algebraMap R K)).toAffine.Nonsingular
      (e (out (WeierstrassIntegralChart.coord W 2 0)))
      (e (out (WeierstrassIntegralChart.coord W 2 1))) := by
  apply (normalized_nonsingular_iff (W.map (algebraMap R K))
    (by simp only [map_a₃, h3, map_mul, hs, zero_mul])
    (by simp only [map_a₄, h4, map_mul, hs, zero_mul])
    (by simp only [map_a₆, h6, map_mul, map_pow, hs, zero_pow (by decide : 2 ≠ 0), zero_mul])
    (WeierstrassIntegralChart.affine_equation_of_hom W (e.comp out))).mpr
  intro h
  apply hx
  simpa only [AlgHom.comp_apply, dividedTangentOutput, WeierstrassIntegralChart.evaluation_coord,
    Matrix.cons_val_zero] using h.1

/-- Nonsingularity of an evaluated tangent gives an actual smooth scheme-valued output. -/
theorem dividedTangent_range_smooth_of_x {K : Type u} [Field K] [Algebra R K]
    (e : T →ₐ[R] K) (hs : algebraMap R K s = 0)
    (hx : e (dividedTangentX W s b3 b4 b6 a c) ≠ 0) :
    Set.range (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ f) ⊆
      WeierstrassIntegralChart.integralSmoothOpen W := by
  let o := e.comp out
  have ho : o ∘ WeierstrassIntegralChart.coord W 2 =
      ![o (WeierstrassIntegralChart.coord W 2 0),
        o (WeierstrassIntegralChart.coord W 2 1), 1] := by
    funext i
    fin_cases i <;> simp
  have hn := dividedTangent_nonsingular_of_x W s b3 b4 b6 a c h3 h4 h6 e hs hx
  have hp := WeierstrassIntegralChart.chartFieldPoint_range_smooth W 2 o
    (by rw [ho]; exact (Projective.nonsingular_some _ _).mpr hn)
  simpa only [dividedTangentToCurve, ← Category.assoc, ← Spec.map_comp,
    o, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, CommRingCat.ofHom_comp] using hp

/-- A source prime with nonzero nodal output abscissa lies in the actual smooth output open. -/
theorem dividedTangent_prime_smooth_of_x (p : PrimeSpectrum T)
    (hs : algebraMap R T s ∈ p.asIdeal)
    (hx : dividedTangentX W s b3 b4 b6 a c ∉ p.asIdeal) :
    f p ∈ WeierstrassIntegralChart.integralSmoothOpen W := by
  let e : T →ₐ[R] p.asIdeal.ResidueField := IsScalarTower.toAlgHom R T _
  have hs0 : algebraMap R p.asIdeal.ResidueField s = 0 := by
    rw [IsScalarTower.algebraMap_apply R T p.asIdeal.ResidueField]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hs
  have hx0 : e (dividedTangentX W s b3 b4 b6 a c) ≠ 0 := by
    exact fun h => hx (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hp : (Spec.map (CommRingCat.ofHom e.toRingHom)) ⟨⊥, inferInstance⟩ = p := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro z
    change algebraMap T p.asIdeal.ResidueField z = 0 ↔ z ∈ p.asIdeal
    exact Ideal.algebraMap_residueField_eq_zero
  have h := dividedTangent_range_smooth_of_x W s b3 b4 b6 a c h3 h4 h6 e hs0 hx0
  exact h ⟨⟨⊥, inferInstance⟩, by rw [Scheme.Hom.comp_apply, hp]⟩

end FLT.Mazur.WeierstrassDilatation
