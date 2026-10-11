/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointScalarMatching

/-!
# Single-point gluing in marked and constant coordinates

A component family glues precisely when its marked class has equal endpoints
and all unmarked scalars are its common endpoint value. These equations refer
to the actual component H0 and the original coefficient trivializations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonSinglePointMatchingCoordinates

open FCurve PolygonPinching PolygonSinglePointLineNormalization
open PolygonNormalizationLinearSections PolygonSinglePointHZeroCoordinates
open PolygonSinglePointScalarMatching

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (j : Fin n) (m : ℕ)

/-- Marked H0 and the independent scalar on each unmarked component. -/
def familyCoordinates : Family K n hn p q h a j m ≃ₗ[K]
    ProjectiveLineMarkedHZero.H0 K a m × ({i : Fin n // i ≠ j} → K) :=
  (linearPiSplitAt _ j).trans ((ownEquiv K n hn p q h a j m).prodCongr
    (LinearEquiv.piCongrRight (otherEquiv K n hn p q h a j m)))

/-- The first coordinate is the original marked component class. -/
theorem familyCoordinates_fst (v : Family K n hn p q h a j m) :
    (familyCoordinates K n hn p q h a j m v).1 = ownEquiv K n hn p q h a j m (v j) := rfl

/-- Each unmarked coordinate is its canonical scalar. -/
theorem familyCoordinates_snd (v : Family K n hn p q h a j m)
    (i : {i : Fin n // i ≠ j}) :
    (familyCoordinates K n hn p q h a j m v).2 i =
      otherEquiv K n hn p q h a j m i (v i.val) := rfl

/-- Actual component matching is equal marked endpoints with the determined unmarked scalars. -/
theorem matching_iff (v : Family K n hn p q h a j m) :
    v ∈ LinearMap.ker (PolygonComponentHZeroMatching.difference K n hn p q h
      (pointPower K n hn p q h a j m)) ↔
      (familyCoordinates K n hn p q h a j m v).1 ∈
        LinearMap.ker (ProjectiveLinePointLoopMatching.difference K a m) ∧
      ∀ i, (familyCoordinates K n hn p q h a j m v).2 i =
        (ProjectiveLineMarkedHZero.polynomialEquiv K a m
          (familyCoordinates K n hn p q h a j m v).1).val.coeff m := by
  constructor
  · intro hv
    constructor
    · rw [ProjectiveLinePointLoopMatching.mem_kernel_iff]
      have he := (matching_constants K n hn p q h a j m v hv j).1.symm
      simpa only [zeroScalar_self, infinityScalar_self, familyCoordinates_fst] using he
    · intro i
      have he := (matching_constants K n hn p q h a j m v hv i.val).2
      simpa only [infinityScalar_other K n hn p q h a j m v i.val i.property, infinityScalar_self,
        familyCoordinates_fst, familyCoordinates_snd] using he
  · rintro ⟨hx, hc⟩
    rw [ProjectiveLinePointLoopMatching.mem_kernel_iff] at hx
    have he (i : Fin n) :
        zeroScalar K n hn p q h a j m v i =
          (ProjectiveLineMarkedHZero.polynomialEquiv K a m
            (ownEquiv K n hn p q h a j m (v j))).val.coeff m ∧
        infinityScalar K n hn p q h a j m v i =
          (ProjectiveLineMarkedHZero.polynomialEquiv K a m
            (ownEquiv K n hn p q h a j m (v j))).val.coeff m := by
      by_cases hi : i = j
      · subst i
        exact ⟨by simpa only [zeroScalar_self, familyCoordinates_fst] using hx.symm,
          by simp only [infinityScalar_self]⟩
      · have hi' := hc ⟨i, hi⟩
        simp only [familyCoordinates_snd, familyCoordinates_fst] at hi'
        exact ⟨by simpa only [zeroScalar_other K n hn p q h a j m v i hi] using hi',
          by simpa only [infinityScalar_other K n hn p q h a j m v i hi] using hi'⟩
    exact (mem_kernel_iff K n hn p q h a j m v).mpr
      (fun i ↦ (he i).1.trans (he (next hn i)).2.symm)

end FLT.Mazur.PolygonSinglePointMatchingCoordinates
