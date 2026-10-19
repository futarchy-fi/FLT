/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointComposition
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Actual point orbits of the full normalized comparison groupoid

The relation uses points of the original comparison scheme, including all its
stabilizers. Transitivity uses a point of the scheme fiber product over matching
endpoints; no joint monomorphism or equivalence closure is imposed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]

/-- Two source points are related by an actual point of the full comparison scheme. -/
def Related (x y : normalizedDisjointSource n) : Prop :=
  ∃ a : disjointComparisonArrows n,
    disjointComparisonSource n a = x ∧ disjointComparisonTarget n a = y

/-- The identity section gives reflexivity on actual source points. -/
theorem related_refl (x : normalizedDisjointSource n) : Related n x x := by
  refine ⟨disjointComparisonIdentity n x, ?_, ?_⟩
  · exact congrArg (fun k ↦ k x) (disjointComparisonIdentity_source n)
  · exact congrArg (fun k ↦ k x) (disjointComparisonIdentity_target n)

/-- The inverse morphism reverses an actual comparison point. -/
theorem related_symm {x y : normalizedDisjointSource n} (h : Related n x y) :
    Related n y x := by
  obtain ⟨a, ha, hb⟩ := h
  refine ⟨disjointComparisonInverse n a, ?_, ?_⟩
  · exact (congrArg (fun k ↦ k a) (disjointComparisonInverse_source n)).trans hb
  · exact (congrArg (fun k ↦ k a) (disjointComparisonInverse_target n)).trans ha

/-- A point above matching endpoints supplies composition without preserving point pullbacks. -/
theorem related_trans {x y z : normalizedDisjointSource n}
    (h : Related n x y) (k : Related n y z) : Related n x z := by
  obtain ⟨a, ha, hb⟩ := h
  obtain ⟨b, hc, hd⟩ := k
  obtain ⟨c, he, hf⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (disjointComparisonTarget n) (disjointComparisonSource n))
    a b (hb.trans hc.symm)
  refine ⟨disjointCompositionMap n c, ?_, ?_⟩
  · exact (congrArg (fun k ↦ k c) (disjointCompositionMap_source n)).trans
      ((congrArg (disjointComparisonSource n) he).trans ha)
  · exact (congrArg (fun k ↦ k c) (disjointCompositionMap_target n)).trans
      ((congrArg (disjointComparisonTarget n) hf).trans hd)

/-- The full comparison relation itself is an equivalence relation on source points. -/
def orbitSetoid : Setoid (normalizedDisjointSource n) where
  r := Related n
  iseqv := ⟨related_refl n, related_symm n, related_trans n⟩

/-- Actual point orbits of the full comparison groupoid. -/
def Orbit := Quotient (orbitSetoid n)

/-- Projection of original source points onto their full comparison orbits. -/
def projection : normalizedDisjointSource n → Orbit n := Quotient.mk (orbitSetoid n)

/-- Orbit equality means that one actual comparison point joins the representatives. -/
theorem projection_eq_iff (x y : normalizedDisjointSource n) :
    projection n x = projection n y ↔ Related n x y := Quotient.eq

/-- Every full comparison orbit has an original source representative. -/
theorem projection_surjective : Function.Surjective (projection n) := Quotient.mk_surjective

/-- Both endpoints of every actual comparison point have the same orbit. -/
theorem projection_pair (a : disjointComparisonArrows n) :
    projection n (disjointComparisonSource n a) = projection n (disjointComparisonTarget n a) :=
  (projection_eq_iff n _ _).mpr ⟨a, rfl, rfl⟩

end FLT.Mazur.CyclicCharacteristicOrbit
