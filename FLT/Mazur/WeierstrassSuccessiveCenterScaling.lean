/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXReesChart
public import FLT.Mazur.WeierstrassModificationCenterCharts

/-!
# Recovering the successive center from the original deeper center

On the preceding divided chart the original center at scale sπ is s times
(π,x,y). A regular scale can be cancelled from ideals even over nonreduced
rings, as needed on affine presentations of smooth translation products.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R]

/-- Multiplication by a regular principal ideal detects equality of arbitrary ideals. -/
theorem regular_principal_mul_cancel {a : R} (ha : IsRegular a) {I J : Ideal R}
    (h : Ideal.span {a} * I = Ideal.span {a} * J) : I = J := by
  have mono {K L : Ideal R} (hKL : Ideal.span {a} * K ≤ Ideal.span {a} * L) : K ≤ L := by
    intro x hx
    obtain ⟨y, hy, he⟩ := Ideal.mem_span_singleton_mul.mp
      (hKL (Ideal.mem_span_singleton_mul.mpr ⟨x, hx, rfl⟩))
    exact ha.left he ▸ hy
  exact le_antisymm (mono h.le) (mono h.ge)

variable (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
  (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6))
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "c" =>
  WeierstrassDilatation.fromOriginal W s (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6

/-- The deeper original center has the exact scale factor on the preceding divided chart. -/
theorem originalCenter_map_fromOriginal :
    (WeierstrassIntegralChart.modificationChartCenter W (s * π) 2).map (c).toRingHom =
      Ideal.span {algebraMap R B s} * modificationCenter W s π b3 b4 b6 := by
  rw [WeierstrassIntegralChart.modificationChartCenter_map]
  simp only [WeierstrassDilatation.fromOriginal_x, WeierstrassDilatation.fromOriginal_y,
    map_mul, modificationCenter, Ideal.span_insert, Ideal.mul_sup,
    Ideal.span_singleton_mul_span_singleton]

/-- The scale factor is retained under every coefficient-compatible affine presentation. -/
theorem originalCenter_map_presentation {S : Type*} [CommRing S] [Algebra R S]
    (f : B →ₐ[R] S) :
    (WeierstrassIntegralChart.modificationChartCenter W (s * π) 2).map
        (f.comp c).toRingHom =
      Ideal.span {algebraMap R S s} * (modificationCenter W s π b3 b4 b6).map f.toRingHom := by
  change (WeierstrassIntegralChart.modificationChartCenter W (s * π) 2).map
    (f.toRingHom.comp (c).toRingHom) = _
  rw [← Ideal.map_map, originalCenter_map_fromOriginal,
    Ideal.map_mul, Ideal.map_span]
  simp only [Set.image_singleton, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]

/-- Equality of the original deeper centers implies equality of the actual successive centers. -/
theorem successiveCenter_eq_of_originalCenter_eq
    {S : Type*} [CommRing S] [Algebra R S] (hs : IsRegular (algebraMap R S s))
    (f g : B →ₐ[R] S)
    (h : (WeierstrassIntegralChart.modificationChartCenter W (s * π) 2).map
        (f.comp c).toRingHom =
      (WeierstrassIntegralChart.modificationChartCenter W (s * π) 2).map
        (g.comp c).toRingHom) :
    (modificationCenter W s π b3 b4 b6).map f.toRingHom =
      (modificationCenter W s π b3 b4 b6).map g.toRingHom := by
  rw [originalCenter_map_presentation, originalCenter_map_presentation] at h
  exact regular_principal_mul_cancel hs h

end FLT.Mazur.WeierstrassSuccessiveX
