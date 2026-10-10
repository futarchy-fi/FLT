/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalCartier
public import FLT.Mazur.PolygonInfinitesimalCoefficientTransport
public import FLT.Mazur.SectionCartesianKernel
public import FLT.Mazur.SectionSumFinite

/-!
# The compatible marked Cartier divisor on an infinitesimal polygon

The sum uses the actual section kernel ideals. It is relative Cartier over any
coefficient ring, and its entire ideal pulls back to the corresponding marked
sum for every coefficient map with a specified image of the smoothing parameter.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open FCurve

variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)

/-- The actual section sum for one specified unit on each cyclic chart. -/
def markingDivisor (a : Fin n → Rˣ) : (scheme R t n h).IdealSheafData :=
  ∏ i, (marking R t n h i (a i)).ker

/-- The marked sum is relative Cartier, including over nonreduced coefficient rings. -/
theorem markingDivisor_cartier (a : Fin n → Rˣ) :
    RelativeEffectiveCartier (toBase R t n h) (markingDivisor R t n h a) :=
  relativeEffectiveCartier_prod _ Finset.univ _ fun i _ ↦ marking_cartier R t n h i (a i)

/-- The divisor contains precisely the marked sections, with no extra support points. -/
theorem markingDivisor_mem_support (a : Fin n → Rˣ) (x : scheme R t n h) :
    x ∈ (markingDivisor R t n h a).support ↔
      ∃ i, x ∈ Set.range (marking R t n h i (a i)) := by
  let _ := PolygonInfinitesimalSeparated.separated R t n h
  change x ∈ (∏ i ∈ Finset.univ, (marking R t n h i (a i)).ker).support ↔ _
  rw [mem_support_prod]
  simp only [Finset.mem_univ, true_and]
  simp only [← SetLike.mem_coe, support_section_ker _ _ (marking_base R t n h _ _)]

variable {R} {S : Type u} [CommRing S] (φ : R →+* S) (s : S)
  [Fact (IsNilpotent s)] (ht : φ t = s)

/-- The full Cartier ideal is compatible with the actual specified coefficient pullback. -/
theorem markingDivisor_parameterProjection (a : Fin n → Rˣ) :
    (markingDivisor R t n h a).comap (parameterProjection φ t s ht n h) =
      markingDivisor S s n h (fun i ↦ Units.map φ (a i)) := by
  let _ := PolygonInfinitesimalSeparated.separated R t n h
  exact section_prod_comap_of_cartesian (parameterProjection_isPullback φ t s ht n h)
    Finset.univ _ _ (fun i ↦ marking_base S s n h i _)
    (fun i ↦ marking_base R t n h i _)
    (fun i ↦ marking_parameterProjection φ t s ht n h i (a i))

end FLT.Mazur.PolygonInfinitesimal
