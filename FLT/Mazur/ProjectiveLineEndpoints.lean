/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineCharts
public import FLT.Mazur.OverPoints

/-!
# Zero and infinity on the projective line

The endpoints are evaluation at zero in the two specified affine charts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial LaurentPolynomial

universe u

namespace FLT.Mazur.ProjectiveLine

variable (K : Type u) [Field K]

/-- Evaluation at zero, regarded as a point of the affine chart. -/
def chartZero : Spec (CommRingCat.of K) ⟶ chart K :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0))

@[reassoc (attr := simp)]
theorem chartZero_toBase : chartZero K ≫ chartToBase K = 𝟙 _ := by
  rw [chartZero, chartToBase, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

/-- Zero is the origin of the first chart. -/
def zero : Spec (CommRingCat.of K) ⟶ scheme K := chartZero K ≫ left K

/-- Infinity is the origin of the second chart. -/
def infinity : Spec (CommRingCat.of K) ⟶ scheme K := chartZero K ≫ right K

@[reassoc (attr := simp)]
theorem zero_toBase : zero K ≫ toBase K = 𝟙 _ := by simp [zero]

@[reassoc (attr := simp)]
theorem infinity_toBase : infinity K ≫ toBase K = 𝟙 _ := by simp [infinity]

/-- The zero section over `Spec K`. -/
def zeroSection : Sections (Over.mk (toBase K)) := Over.homMk (zero K) (zero_toBase K)

/-- The infinity section over `Spec K`. -/
def infinitySection : Sections (Over.mk (toBase K)) :=
  Over.homMk (infinity K) (infinity_toBase K)

theorem chartZero_not_overlap (x : overlap K) :
    overlapLeft K x ≠ chartZero K (default : Spec (CommRingCat.of K)) := by
  intro h
  have hX : (Polynomial.X : K[X]) ∈
      (chartZero K (default : Spec (CommRingCat.of K))).asIdeal := by
    change Polynomial.eval 0 Polynomial.X ∈ (⊥ : Ideal K)
    simp
  rw [← h] at hX
  change Polynomial.toLaurent Polynomial.X ∈ x.asIdeal at hX
  have := x.isPrime
  exact x.asIdeal.notMem_of_isUnit (by simpa using LaurentPolynomial.isUnit_T (R := K) 1) hX

/-- Zero and infinity have different underlying scheme points. -/
theorem zero_point_ne_infinity :
    zero K (default : Spec (CommRingCat.of K)) ≠
      infinity K (default : Spec (CommRingCat.of K)) := by
  intro h
  obtain ⟨i, fi, fj, x, hx, _⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (span (overlapLeft K) (overlapRight K))).mp h
  cases i with
  | none =>
    cases fi
    exact chartZero_not_overlap K x hx
  | some i =>
    cases i with
    | left => cases fj
    | right => cases fi

/-- The two specified morphisms from `Spec K` are distinct. -/
theorem zero_ne_infinity : zero K ≠ infinity K := by
  intro h
  exact zero_point_ne_infinity K (congrArg
    (fun f : Spec (CommRingCat.of K) ⟶ scheme K ↦ f default) h)

/-- The two endpoints are distinct as sections over the base. -/
theorem zeroSection_ne_infinitySection : zeroSection K ≠ infinitySection K := by
  intro h
  exact zero_ne_infinity K (congrArg (fun s ↦ s.left) h)

end FLT.Mazur.ProjectiveLine
