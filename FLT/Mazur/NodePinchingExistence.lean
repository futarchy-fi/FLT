/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeLocalDescent
public import FLT.Mazur.TernaryOpenDescent

/-!
# Existence of descent from the two node branches

The saturated neighborhood descends to an arbitrary target and glues to
the two punctured branches. This file proves existence; uniqueness is separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial

universe u

namespace FLT.Mazur.NodePinchingExistence

open PolygonNodeEqualizer PolygonNodePresentation NodeLocalDescent

/-- A cartesian normalization square turns agreement into overlap compatibility. -/
theorem compatible {S D L T X Y : Scheme.{u}}
    (a : S ⟶ L) (b : S ⟶ D) (c : L ⟶ X) (i : D ⟶ X)
    (l : T ⟶ L) (j : T ⟶ X)
    (sq : IsPullback a b c i) (hj : l ≫ c = j)
    (f : L ⟶ Y) (d : D ⟶ Y) (hd : b ≫ d = a ≫ f) :
    pullback.fst i j ≫ d = pullback.snd i j ≫ (l ≫ f) := by
  have w : (pullback.snd i j ≫ l) ≫ c = pullback.fst i j ≫ i := by
    rw [Category.assoc, hj, pullback.condition]
  let t := sq.lift (pullback.snd i j ≫ l) (pullback.fst i j) w
  calc
    _ = (t ≫ b) ≫ d := by rw [IsPullback.lift_snd]
    _ = t ≫ a ≫ f := by rw [Category.assoc, hd]
    _ = _ := by rw [← Category.assoc, IsPullback.lift_fst, Category.assoc]

variable (K : Type u) [Field K]

instance branchOpen_isOpenImmersion (p : K[X]) : IsOpenImmersion (branchOpen K p) :=
  IsOpenImmersion.of_isLocalization p

/-- A normalized principal neighborhood and the punctured line cover the line. -/
theorem line_covers (p : K[X]) (hp : p.eval 0 = 1) (z : ProjectiveLine.chart K) :
    z ∈ Set.range (branchOpen K p) ∨ z ∈ Set.range (ProjectiveLine.overlapLeft K) := by
  rw [show Set.range (branchOpen K p) =
    (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range (Localization.Away p) p]
  rw [show Set.range (ProjectiveLine.overlapLeft K) =
    (PrimeSpectrum.basicOpen (X : K[X]) : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range K[T;T⁻¹] X]
  change p ∉ z.asIdeal ∨ X ∉ z.asIdeal
  by_contra h
  have h' : p ∈ z.asIdeal ∧ X ∈ z.asIdeal := by simpa using h
  have hdiv : (X : K[X]) ∣ p - 1 := by
    rw [X_dvd_iff]
    simp [coeff_zero_eq_eval_zero, hp]
  have hm := z.asIdeal.mem_of_dvd hdiv h'.2
  have hone : (1 : K[X]) ∈ z.asIdeal := by simpa using z.asIdeal.sub_mem h'.1 hm
  exact z.isPrime.one_notMem hone

/-- Every pair of node branch maps agreeing at the origin descends to any scheme. -/
theorem exists_desc {Y : Scheme.{u}} (f g : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃ d : PolygonNodeBranches.node K ⟶ Y,
      PolygonCyclicAtlas.firstBranch K ≫ d = f ∧
      PolygonCyclicAtlas.secondBranch K ≫ d = g := by
  obtain ⟨s, hs, d, hd₁, hd₂⟩ := exists_local_desc K f g w
  let i := neighborhood K s hs
  let j := PolygonNodeBranches.left K
  let k := PolygonNodeBranches.right K
  let f' := ProjectiveLine.overlapLeft K ≫ f
  let g' := ProjectiveLine.overlapLeft K ≫ g
  have h₁ : pullback.fst i j ≫ d = pullback.snd i j ≫ f' :=
    compatible _ _ _ _ _ _ (first_isPullback K s hs)
      (PolygonCyclicAtlas.overlap_firstBranch K) f d hd₁
  have h₂ : pullback.fst i k ≫ d = pullback.snd i k ≫ g' :=
    compatible _ _ _ _ _ _ (second_isPullback K s hs)
      (PolygonCyclicAtlas.overlap_secondBranch K) g d hd₂
  have h₃ : pullback.fst j k ≫ f' = pullback.snd j k ≫ g' :=
    TernaryOpenDescent.disjoint_compatible j k f' g' (PolygonNodeBranches.disjoint_ranges K)
  let e := TernaryOpenDescent.desc i j k (covers K s hs) d f' g' h₁ h₂ h₃
  have he₁ : i ≫ e = d := TernaryOpenDescent.first_desc ..
  have he₂ : j ≫ e = f' := TernaryOpenDescent.second_desc ..
  have he₃ : k ≫ e = g' := TernaryOpenDescent.third_desc ..
  refine ⟨e, ?_, ?_⟩
  · apply BinaryOpenDescent.hom_ext (branchOpen K (first s)) (ProjectiveLine.overlapLeft K)
      (line_covers K (first s) (NodeLocalizedEqualizer.first_value s hs))
    · rw [← Category.assoc, ← firstBranch_neighborhood, Category.assoc, he₁]
      exact hd₁
    · simpa only [PolygonCyclicAtlas.overlap_firstBranch_assoc] using he₂
  · apply BinaryOpenDescent.hom_ext (branchOpen K (second s)) (ProjectiveLine.overlapLeft K)
      (line_covers K (second s) (NodeLocalizedEqualizer.second_value s hs))
    · rw [← Category.assoc, ← secondBranch_neighborhood, Category.assoc, he₁]
      exact hd₂
    · simpa only [PolygonCyclicAtlas.overlap_secondBranch_assoc] using he₃

end FLT.Mazur.NodePinchingExistence
