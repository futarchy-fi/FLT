/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCoordinateCotangent
public import FLT.GroupScheme.PDivisibleCotangentRepresentativeLift

/-! # Compatible coordinate functions lifting the original cotangent limit

These are functions in the original representing algebra, with prescribed cotangent
classes. Power-series generation and analytic convergence are separate obligations.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Every original cotangent vector is the derivative of an actual compatible function.
Successive quadratic corrections preserve previously chosen finite coordinates. -/
theorem coordinateCotangent_surjective : Function.Surjective X.coordinateCotangent := by
  intro v
  let F (n : ℕ) := {a : (X.level n).cotangentIdeal //
    (X.level n).cotangentIdeal.toCotangent a = X.cotangentEval n v}
  have step (n : ℕ) (a : F n) :
      ∃ b : F (n + 1), X.inclusion (Nat.le_succ n) b.val = a.val := by
    have hv : (X.inclusion (Nat.le_succ n)).cotangentMap (X.cotangentEval (n + 1) v) =
        (X.level n).cotangentIdeal.toCotangent a.val :=
      (X.cotangentEval_restriction (Nat.le_succ n) v).trans a.property.symm
    obtain ⟨b, hb, hc⟩ := (X.inclusion (Nat.le_succ n)).exists_cotangent_representative_lift
      (X.closed (Nat.le_succ n)) a.val (X.cotangentEval (n + 1) v) hv
    exact ⟨⟨b, hc⟩, hb⟩
  obtain ⟨a, ha⟩ := (X.level 0).cotangentIdeal.toCotangent_surjective (X.cotangentEval 0 v)
  let s : ∀ n, F n := fun n ↦ Nat.rec (⟨a, ha⟩ : F 0) (fun n b ↦ (step n b).choose) n
  have hs (n : ℕ) : X.inclusion (Nat.le_succ n) (s (n + 1)).val = (s n).val :=
    (step n (s n)).choose_spec
  have hall {m n : ℕ} (h : m ≤ n) : X.inclusion h (s n).val = (s m).val := by
    induction n, h using Nat.le_induction with
    | base => rw [X.inclusion_refl]; rfl
    | succ n h ih =>
      rw [← X.inclusion_comp h (Nat.le_succ n)]
      change X.inclusion h (X.inclusion (Nat.le_succ n) (s (n + 1)).val) = _
      rw [hs, ih]
  let x : X.coordinateLimit := ⟨fun n ↦ (s n).val.val, fun h ↦ hall h⟩
  have hx : x ∈ X.coordinateAugmentationIdeal := (s 0).val.property
  refine ⟨⟨x, hx⟩, ?_⟩
  apply X.cotangentLimit_ext
  intro n
  exact (s n).property

/-- A chosen family of original cotangent classes has simultaneous lifts to actual functions. -/
theorem exists_coordinate_parameters {ι : Type*} (v : ι → X.cotangentLimit) :
    ∃ x : ι → X.coordinateAugmentationIdeal, ∀ i, X.coordinateCotangent (x i) = v i := by
  choose x hx using fun i ↦ X.coordinateCotangent_surjective (v i)
  exact ⟨x, hx⟩

/-- The original cotangent module is recovered as the quotient by functions quadratic
at every original finite level. -/
def coordinateCotangentQuotientEquiv :
    (X.coordinateAugmentationIdeal ⧸ LinearMap.ker X.coordinateCotangent) ≃ₗ[R]
      X.cotangentLimit :=
  X.coordinateCotangent.quotKerEquivOfSurjective X.coordinateCotangent_surjective

/-- The quotient equivalence is the derivative computed in the original finite coordinates. -/
theorem coordinateCotangentQuotientEquiv_mk (x : X.coordinateAugmentationIdeal) :
    X.coordinateCotangentQuotientEquiv (Submodule.Quotient.mk x) = X.coordinateCotangent x := rfl

end ThreeAdicPlan.PDivisibleSystem
