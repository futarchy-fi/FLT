/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRamifiedCoefficientDepths
public import FLT.Mazur.UniformizerRootExtension

/-!
# A degree-at-most-six semistable model for a short equation

A fourth or sixth root of the base uniformizer clears the smaller weighted
coefficient depth. The constructed integral equation has unit discriminant
or unit c₄, and an explicit variable change identifies its generic fiber
with the original curve over the constructed finite field extension.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsDiscreteValuationRing

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Construct a finite ramified extension and an integral short model with semistable invariants. -/
theorem exists_short_semistable_extension (W : WeierstrassCurve R) [W.IsShortNF]
    (hΔ : W.Δ ≠ 0) (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    {π : R} (hπ : Irreducible π) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra R L) (_ : IsScalarTower R K L) (S : Type u) (_ : CommRing S)
      (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S L) (_ : IsScalarTower R S L)
      (_ : IsFractionRing S L) (_ : IsIntegralClosure S R L)
      (U : WeierstrassCurve S) (C : VariableChange L),
      Module.finrank K L ≤ 6 ∧
      addVal S (algebraMap R S π) = (Module.finrank K L : ℕ∞) ∧
      U.IsShortNF ∧ (IsUnit U.Δ ∨ IsUnit U.c₄) ∧
      C • W.map (algebraMap R L) = U.map (algebraMap S L) := by
  have hfinite : addVal R W.a₄ ≠ ⊤ ∨ addVal R W.a₆ ≠ ⊤ := by
    by_contra h
    push Not at h
    have h4 := addVal_eq_top_iff.mp h.1
    have h6 := addVal_eq_top_iff.mp h.2
    apply hΔ
    rw [Δ_of_isShortNF, h4, h6]
    ring
  obtain ⟨e, m, he, hv4, hv6, hs⟩ :=
    short_ramified_depths (addVal R W.a₄) (addVal R W.a₆) hfinite
  have hepos : 0 < e := by rcases he with rfl | rfl <;> decide
  have hele : e ≤ 6 := by rcases he with rfl | rfl <;> decide
  obtain ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, ρ, hdeg, hρ, _, hval, _⟩ := exists_uniformizerRoot_extension (K := K) hπ hepos
  let V := W.map (algebraMap R S)
  have : V.IsShortNF := ⟨by simp [V, map_a₁],
    by simp [V], by simp [V, map_a₃]⟩
  have hV4 : addVal S V.a₄ = e • addVal R W.a₄ :=
    addVal_map_of_uniformizer (algebraMap R S) hπ hepos hval W.a₄
  have hV6 : addVal S V.a₆ = e • addVal R W.a₆ :=
    addVal_map_of_uniformizer (algebraMap R S) hπ hepos hval W.a₆
  obtain ⟨U, hU, hu4, hu6, hu⟩ := exists_short_weighted_unit_model V hρ m
    (hV4.symm ▸ hv4) (hV6.symm ▸ hv6) (by rwa [hV4, hV6])
    (by simpa only [map_ofNat] using h2.map (algebraMap R S))
    (by simpa only [map_ofNat] using h3.map (algebraMap R S))
  let : U.IsShortNF := hU
  have hr : algebraMap S L ρ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr hρ.ne_zero
  let C : VariableChange L :=
    ⟨Units.mk0 (algebraMap S L (ρ ^ m)) (by simpa using pow_ne_zero m hr), 0, 0, 0⟩
  refine ⟨L, hL, aK, fin, aR, towerK, S, hS, dom, dvr, aS, finS, aSL, towerS,
    frac, closure, U, C, hdeg ▸ hele, by simpa only [hdeg] using hval, hU, hu, ?_⟩
  have hc := short_weighted_model_variableChange (algebraMap S L) V U hr m hu4 hu6
  simpa only [V, map_map, ← IsScalarTower.algebraMap_eq R S L] using hc

end FLT.Mazur
