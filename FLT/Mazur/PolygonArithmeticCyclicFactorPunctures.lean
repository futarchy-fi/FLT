/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicFactors

/-!
# Full punctures and edge transport of the accumulated cyclic factors

Every finite edge square uses both punctures of the same whole-node factors.
No separate boundary isomorphisms are chosen after the node construction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (σ : Equiv.Perm ι) (S : State R π ι) (hS : S.Compatible) (ha : S.Annihilated)
  (r₀ : ℕ) (hr₀ : S.Normalized r₀) (m : ℕ)
local notation "U" => S.iterateAux σ hS ha r₀ hr₀
local notation "F" => S.iterateSelectedFieldAux σ hS ha r₀ hr₀
local notation "N" => S.iterateNodeFactorAux σ hS ha r₀ hr₀ m
local notation "P" => S.iteratePunctureFactorAux σ hS ha r₀ hr₀ m

/-- Both accumulated punctures are induced by the same full finite node equivalence. -/
theorem State.iterateNodeFactorAux_puncture (i : ι) (a : Bool) (k : ℕ) :
    (punctureLaurentMap (S.parameter m i) a).comp (N i k).toAlgHom =
      (P i a k).toAlgHom.comp (punctureLaurentMap ((U k).val.parameter m i) a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (punctureLaurentMap (S.parameter m i) a).comp ((N i k).toAlgHom.comp
      ((U k).val.nodeFactor σ (F k) (r₀ + k) m i).toAlgHom) =
      ((P i a k).toAlgHom.comp
        ((U k).val.punctureFactor σ (F k) (r₀ + k) m i a).toAlgHom).comp _
    rw [← AlgHom.comp_assoc, ih, AlgHom.comp_assoc, State.nodeFactor_puncture,
      ← AlgHom.comp_assoc]
    rfl

/-- The full finite edge square transports the original edge through its incident factors. -/
theorem State.iteratePunctureFactorAux_edge (i : ι) (k : ℕ) :
    ((U k).val.edge m i).trans (P i true k) =
      (P (σ i) false k).trans (S.edge m i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    ext z : 1
    change P i true k
      (((U k).val.punctureFactor σ (F k) (r₀ + k) m i true)
        (((U k).val.punctureFactor σ (F k) (r₀ + k) m i true).symm
          ((U k).val.edge m i
            (((U k).val.punctureFactor σ (F k) (r₀ + k) m (σ i) false) z)))) = _
    rw [AlgEquiv.apply_symm_apply]
    exact DFunLike.congr_fun ih
      (((U k).val.punctureFactor σ (F k) (r₀ + k) m (σ i) false) z)

attribute [local irreducible] State.iterateAux State.iterateNodeFactorAux
  State.iteratePunctureFactorAux

/-- Parameter transport in the sealed whole-node factor preserves both full punctures. -/
theorem State.iterateNodeFactor_puncture (k : ℕ) (i : ι) (a : Bool) :
    (punctureLaurentMap (S.parameter m i) a).comp
        (S.iterateNodeFactor σ hS ha r₀ hr₀ k m i).toAlgHom =
      (S.iteratePunctureFactor σ hS ha r₀ hr₀ k m i a).toAlgHom.comp
        (punctureLaurentMap ((S.iterate σ hS ha r₀ hr₀ k).parameter m i) a) := by
  rw [State.iterateNodeFactor_def, State.iteratePunctureFactor_def]
  change (punctureLaurentMap _ a).comp
    ((N i k).toAlgHom.comp (nodeParameterEquiv _ _ _).toAlgHom) = _
  rw [← AlgHom.comp_assoc, State.iterateNodeFactorAux_puncture,
    AlgHom.comp_assoc, punctureLaurentMap_parameter]

/-- The sealed finite factors retain every full seed edge. -/
theorem State.iteratePunctureFactor_edge (k : ℕ) (i : ι) :
    ((S.iterate σ hS ha r₀ hr₀ k).edge m i).trans
        (S.iteratePunctureFactor σ hS ha r₀ hr₀ k m i true) =
      (S.iteratePunctureFactor σ hS ha r₀ hr₀ k m (σ i) false).trans (S.edge m i) := by
  rw [State.iterate_def, State.iteratePunctureFactor_def, State.iteratePunctureFactor_def]
  exact S.iteratePunctureFactorAux_edge σ hS ha r₀ hr₀ m i k

end FLT.Mazur.PolygonArithmeticCyclic
