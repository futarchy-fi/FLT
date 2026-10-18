/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicFactorPunctures
public import FLT.Mazur.PolygonArithmeticCyclicDiagonal
public import FLT.Mazur.PolygonSmoothingPunctureSquare

/-!
# Quotient compatibility of the diagonal whole-node factors

Stabilization permits the number of factors to change across the arithmetic
quotient. Joint detection on both punctures supplies the full node square.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (σ : Equiv.Perm ι) (S : State R π ι) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized r₀)
local notation "U" => S.iterateAux σ hS ha r₀ hr₀
local notation "F" => S.iterateSelectedFieldAux σ hS ha r₀ hr₀
local notation "P" => S.iteratePunctureFactorAux σ hS ha r₀ hr₀

/-- Expose finite compatibility without expanding the recursively constructed proof tuple. -/
theorem State.iterateAux_compatible (k : ℕ) : (U k).val.Compatible := (U k).property.1

attribute [local irreducible] State.iterateAux

/-- Both full finite punctures retain the original coefficient square. -/
theorem State.iteratePunctureFactorAux_compatible (i : ι) (a : Bool) (k : ℕ) :
    CompatibleEquiv (fun m ↦ P m i a k) := by
  induction k with
  | zero => intro m; rfl
  | succ k ih =>
    intro m
    apply punctureEquiv_trans_naturality
    · exact (U k).val.punctureFactor_compatible σ (F k) (r₀ + k)
        (S.iterateAux_compatible σ hS ha r₀ hr₀ k) i a m
    · exact ih m

/-- Adding later whole-node factors leaves the complete earlier punctures unchanged. -/
theorem State.iteratePunctureFactorAux_stable (m : ℕ) {k l : ℕ}
    (hkl : k ≤ l) (hm : m ≤ r₀ + k) (i : ι) (a : Bool) : P m i a l = P m i a k := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [State.iteratePunctureFactorAux,
      State.punctureFactor_stable σ (F l) (U l).val (r₀ + l) m (by omega)]
    exact ih

/-- Both diagonal punctures retain the full quotient square despite the changing factor count. -/
theorem State.diagonalPunctureFactor_compatible (i : ι) (a : Bool) :
    CompatibleEquiv (fun m ↦ S.iteratePunctureFactor σ hS ha r₀ hr₀ m m i a) := by
  intro m
  simp only [State.iteratePunctureFactor_def]
  have h := S.iteratePunctureFactorAux_compatible σ hS ha r₀ hr₀ i a (m + 1) m
  dsimp only at h
  rw [S.iteratePunctureFactorAux_stable σ hS ha r₀ hr₀ m
    (Nat.le_succ m) (by omega) i a] at h
  exact h

local notation "D" => S.diagonal σ hS ha r₀ hr₀
local notation "hD" => S.diagonal_compatible σ hS ha r₀ hr₀

/-- The full diagonal node factors, including both coordinates, respect the original quotients. -/
theorem State.diagonalNodeFactor_restriction (m : ℕ) (i : ι) :
    (ringMap (restriction R π m).toRingHom (S.parameter (m + 1) i)
      (S.parameter m i) (hS.1 m i)).comp
        (S.iterateNodeFactor σ hS ha r₀ hr₀ (m + 1) (m + 1) i).toRingHom =
      (S.iterateNodeFactor σ hS ha r₀ hr₀ m m i).toRingHom.comp
        (ringMap (restriction R π m).toRingHom ((D).parameter (m + 1) i)
          ((D).parameter m i) ((hD).1 m i)) := by
  apply punctureFactor_coefficientSquare
    (a := fun a ↦ S.iteratePunctureFactor σ hS ha r₀ hr₀ (m + 1) (m + 1) i a)
    (d := fun a ↦ S.iteratePunctureFactor σ hS ha r₀ hr₀ m m i a)
  · exact fun a ↦ S.iterateNodeFactor_puncture σ hS ha r₀ hr₀ (m + 1) (m + 1) i a
  · exact fun a ↦ S.iterateNodeFactor_puncture σ hS ha r₀ hr₀ m m i a
  · exact fun a ↦ S.diagonalPunctureFactor_compatible σ hS ha r₀ hr₀ i a m

end FLT.Mazur.PolygonArithmeticCyclic
