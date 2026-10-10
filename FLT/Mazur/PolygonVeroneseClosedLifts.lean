/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleVeroneseMultiplication
public import FLT.Mazur.PolygonInfinitesimalStageAmple
public import FLT.Mazur.PolygonInfinitesimalStageProper
public import FLT.Mazur.PolygonVeroneseDegreeExactness
public import FLT.Mazur.PolygonVeroneseProductLifting

/-!
# Lifting every closed homogeneous degree from bounded compatible generators

Actual closed multiplication generation lowers the degree by a fixed
positive amount. Strong induction lifts every closed section into any
subalgebra containing all compatible sections in a bounded range.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family compatibleEval boundarySeriesScalars

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Bounded original compatible degrees suffice to lift every actual closed homogeneous section. -/
theorem exactVeronese_closed_lifts_from_bounded : ∃ B : ℕ,
    ∀ A : Subalgebra (PowerSeries K)
      (CompatibleVeroneseSections K n h (exactVeroneseStep K n h)),
    (∀ d < B, ∀ t : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d,
      (DirectSum.of _ d t :
        CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) ∈ A) →
    ∀ d (s : boundarySeriesDegree K n h 0 (exactVeroneseStep K n h * d)),
      ∃ t : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d,
        DirectSum.of _ d t ∈ A ∧
          compatibleDegreeEval K n h 0 (exactVeroneseStep K n h * d) t = s := by
  obtain ⟨a, ha, I, hI, s, B, hB⟩ :=
    (boundaryLine_ample K 0 n h).exists_veronese_multiplication_generators
      (family K 0 n h).hom (exactVeroneseStep K n h) (exactVeroneseStep_pos K n h)
  let _ := hI
  refine ⟨a + B + 1, fun A hA ↦ ?_⟩
  have hlift (d : ℕ)
      (v : Γ(tensorPower (boundaryLine K 0 n h) (exactVeroneseStep K n h * d), ⊤)) :
      ∃ t : compatibleVeroneseDegree K n h (exactVeroneseStep K n h) d,
        (DirectSum.of _ d t :
          CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) ∈ A ∧
        compatibleEval K n h 0 t =
          of (boundaryLine K 0 n h) ⊤ (exactVeroneseStep K n h * d) v := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      by_cases hd : d < a + B + 1
      · obtain ⟨t, ht⟩ := exactVeroneseDegree_surjective K n h d 0
          ⟨of (boundaryLine K 0 n h) ⊤ (exactVeroneseStep K n h * d) v, ⟨v, rfl⟩⟩
        exact ⟨t, hA d hd t, congrArg Subtype.val ht⟩
      · obtain ⟨b, rfl⟩ : ∃ b, d = a + b := ⟨d - a, by omega⟩
        obtain ⟨t, ht⟩ := hB b (by omega) v
        have hxlift := fun i : I ↦ ih a (by omega) (s i)
        have hylift := fun i : I ↦ ih b (by omega) (t i)
        choose x hx hxval using hxlift
        choose y hy hyval using hylift
        obtain ⟨u, hu, he⟩ := compatibleVeronese_product_sum_lift K n h
          (exactVeroneseStep K n h) a b A x y hx hy
        refine ⟨u, hu, (he 0).trans ?_⟩
        simpa only [hxval, hyval] using ht.symm
  intro d v
  obtain ⟨s, hs⟩ := v.property
  obtain ⟨t, ht, he⟩ := hlift d s
  exact ⟨t, ht, Subtype.ext (he.trans hs)⟩

end FLT.Mazur.PolygonInfinitesimalStages
