/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AmpleVeroneseMultiplication
public import FLT.Mazur.PolygonArithmeticBoundaryAmple
public import FLT.Mazur.PolygonArithmeticStageProper
public import FLT.Mazur.PolygonArithmeticVeroneseExactness
public import FLT.Mazur.PolygonArithmeticProductLifting

/-!
# Lifting every closed homogeneous degree from bounded compatible generators

Actual closed multiplication generation lowers the degree by a fixed
positive amount. Strong induction lifts every closed section into any
subalgebra containing all compatible sections in a bounded range.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve ModuleLineBundleTensorPullback SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family compatibleEval boundaryIntegralScalars

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Bounded original compatible degrees suffice to lift every actual closed homogeneous section. -/
theorem exactVeronese_closed_lifts_from_bounded : ∃ B : ℕ,
    ∀ S : Subalgebra (A)
      (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)),
    (∀ d < B, ∀ t : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d,
      (DirectSum.of _ d t :
        CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) ∈ S) →
    ∀ d (s : boundaryIntegralDegree A π n h 0 (exactVeroneseStep A π hne hgen n h * d)),
      ∃ t : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d,
        DirectSum.of _ d t ∈ S ∧
          compatibleDegreeEval A π n h 0 (exactVeroneseStep A π hne hgen n h * d) t = s := by
  let _ := family_proper A π hgen 0 n h
  obtain ⟨a, ha, I, hI, s, B, hB⟩ :=
    (boundaryLine_ample A π hgen 0 n h).exists_veronese_multiplication_generators
      (family A π 0 n h).hom (exactVeroneseStep A π hne hgen n h) (exactVeroneseStep_pos A π
      hne hgen n h)
  let _ := hI
  refine ⟨a + B + 1, fun S hA ↦ ?_⟩
  have hlift (d : ℕ)
      (v : Γ(tensorPower (boundaryLine A π 0 n h) (exactVeroneseStep A π hne hgen n h * d), ⊤)) :
      ∃ t : compatibleVeroneseDegree A π n h (exactVeroneseStep A π hne hgen n h) d,
        (DirectSum.of _ d t :
          CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) ∈ S ∧
        compatibleEval A π n h 0 t =
          of (boundaryLine A π 0 n h) ⊤ (exactVeroneseStep A π hne hgen n h * d) v := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      by_cases hd : d < a + B + 1
      · obtain ⟨t, ht⟩ := exactVeroneseDegree_surjective A π hne hgen n h d 0
          ⟨of (boundaryLine A π 0 n h) ⊤ (exactVeroneseStep A π hne hgen n h * d) v, ⟨v, rfl⟩⟩
        exact ⟨t, hA d hd t, congrArg Subtype.val ht⟩
      · obtain ⟨b, rfl⟩ : ∃ b, d = a + b := ⟨d - a, by omega⟩
        obtain ⟨t, ht⟩ := hB b (by omega) v
        have hxlift := fun i : I ↦ ih a (by omega) (s i)
        have hylift := fun i : I ↦ ih b (by omega) (t i)
        choose x hx hxval using hxlift
        choose y hy hyval using hylift
        obtain ⟨u, hu, he⟩ := compatibleVeronese_product_sum_lift A π n h
          (exactVeroneseStep A π hne hgen n h) a b S x y hx hy
        refine ⟨u, hu, (he 0).trans ?_⟩
        simpa only [hxval, hyval] using ht.symm
  intro d v
  obtain ⟨s, hs⟩ := v.property
  obtain ⟨t, ht, he⟩ := hlift d s
  exact ⟨t, ht, Subtype.ext (he.trans hs)⟩

end FLT.Mazur.PolygonArithmeticStages
