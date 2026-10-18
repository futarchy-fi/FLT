/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicIteration
public import FLT.Mazur.PolygonSmoothingParameterEquiv

/-!
# Whole-node factors for the cyclic normalization

Compose the actual factors on their changing smoothing rings. The resulting
isomorphisms retain the whole seed nodes, not only their torus boundaries.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (σ : Equiv.Perm ι) (S : State R π ι) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized r₀)
local notation "U" => S.iterateAux σ hS ha r₀ hr₀
local notation "I" => S.iterate σ hS ha r₀ hr₀

/-- The actual fields chosen from the preceding finite cyclic state. -/
def State.iterateSelectedFieldAux (k : ℕ) : ι → R[T;T⁻¹] :=
  let prev := U k
  prev.val.nextIntegralField prev.property.1 (r₀ + k) prev.property.2.2

local notation "F" => S.iterateSelectedFieldAux σ hS ha r₀ hr₀

/-- Compose complete node factors along the actual changing finite smoothings. -/
def State.iterateNodeFactorAux (m : ℕ) (i : ι) : (k : ℕ) →
    ChartRing ((U k).val.parameter m i) ≃ₐ[Quotient R π m] ChartRing (S.parameter m i)
  | 0 => AlgEquiv.refl
  | k + 1 => ((U k).val.nodeFactor σ (F k) (r₀ + k) m i).trans
      (State.iterateNodeFactorAux m i k)

/-- Compose both puncture substitutions of those same whole-node factors. -/
def State.iteratePunctureFactorAux (m : ℕ) (i : ι) (a : Bool) : (k : ℕ) →
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹]
  | 0 => AlgEquiv.refl
  | k + 1 => ((U k).val.punctureFactor σ (F k) (r₀ + k) m i a).trans
      (State.iteratePunctureFactorAux m i a k)

attribute [local irreducible] State.iterateAux State.iterateNodeFactorAux
  State.iteratePunctureFactorAux

/-- Seal the full node comparison on the exact finite-state parameter. -/
irreducible_def State.iterateNodeFactor (k m : ℕ) (i : ι) :
    ChartRing ((I k).parameter m i) ≃ₐ[Quotient R π m] ChartRing (S.parameter m i) :=
  (nodeParameterEquiv _ _ (congrArg (fun V : State R π ι ↦ V.parameter m i)
    (S.iterate_def σ hS ha r₀ hr₀ k))).trans
      (S.iterateNodeFactorAux σ hS ha r₀ hr₀ m i k)

/-- Seal both full punctures of the accumulated whole-node correction. -/
irreducible_def State.iteratePunctureFactor (k m : ℕ) (i : ι) (a : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  S.iteratePunctureFactorAux σ hS ha r₀ hr₀ m i a k

end FLT.Mazur.PolygonArithmeticCyclic
