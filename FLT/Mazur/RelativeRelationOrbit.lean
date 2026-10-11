/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Point orbits of an internal relative scheme equivalence relation

Transitivity uses existence of a scheme point over a pair of points in a
fiber product. The underlying-point functor does not preserve pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- Two source points lie in the same orbit if an actual relation point joins them. -/
def Related (p q : A ⟶ U) (x y : U.left) : Prop :=
  ∃ a : A.left, p.left a = x ∧ q.left a = y

include e

/-- The diagonal relation gives reflexivity on scheme points. -/
theorem related_refl (x : U.left) : Related p q x x := by
  refine ⟨e.r.left x, ?_, ?_⟩
  · exact congrArg (fun k ↦ k.left x) e.reflexivity₁
  · exact congrArg (fun k ↦ k.left x) e.reflexivity₂

/-- The internal inverse reverses an actual relation point. -/
theorem related_symm {x y : U.left} (h : Related p q x y) : Related p q y x := by
  obtain ⟨a, ha, hb⟩ := h
  refine ⟨e.s.left a, ?_, ?_⟩
  · exact (congrArg (fun k ↦ k.left a) e.symmetry₁).trans hb
  · exact (congrArg (fun k ↦ k.left a) e.symmetry₂).trans ha

/-- Internal composition gives transitivity, using surjectivity onto the point fiber product. -/
theorem related_trans {x y z : U.left} (h : Related p q x y) (k : Related p q y z) :
    Related p q x z := by
  obtain ⟨a, ha, hb⟩ := h
  obtain ⟨b, hc, hd⟩ := k
  have hp := (IsPullback.of_isLimit e.isLimit).map (Over.forget S)
  obtain ⟨c, he, hf⟩ := Scheme.exists_preimage_of_isPullback hp a b (hb.trans hc.symm)
  refine ⟨e.t.left c, ?_, ?_⟩
  · calc
      p.left (e.t.left c) = p.left (e.c.fst.left c) :=
        congrArg (fun k ↦ k.left c) e.transitivity₁
      _ = x := (congrArg p.left he).trans ha
  · calc
      q.left (e.t.left c) = q.left (e.c.snd.left c) :=
        congrArg (fun k ↦ k.left c) e.transitivity₂
      _ = z := (congrArg q.left hf).trans hd

/-- The actual relation on points, without adding an equivalence closure. -/
def orbitSetoid : Setoid U.left where
  r := Related p q
  iseqv := ⟨related_refl e, related_symm e, related_trans e⟩

/-- The type of actual point orbits of the relative scheme relation. -/
def Orbit := Quotient (orbitSetoid e)

/-- The projection from the actual source points to their orbits. -/
def projection : U.left → Orbit e := Quotient.mk (orbitSetoid e)

/-- Equality in the constructed orbit type is precisely the original point relation. -/
theorem projection_eq_iff (x y : U.left) :
    projection e x = projection e y ↔ Related p q x y := Quotient.eq

/-- Every orbit has a source point. -/
theorem projection_surjective : Function.Surjective (projection e) := Quotient.mk_surjective

/-- The two original projections give the same orbit. -/
theorem projection_pair (a : A.left) : projection e (p.left a) = projection e (q.left a) :=
  (projection_eq_iff e _ _).mpr ⟨a, rfl, rfl⟩

end FLT.Mazur.RelativeRelationOrbit
