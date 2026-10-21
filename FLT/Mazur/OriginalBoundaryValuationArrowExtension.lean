/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFiniteValuationArrows
public import FLT.Mazur.OriginalBoundaryComparisonNeighborhood

/-!
# Extending actual original boundary arrows across a valuation ring

A generic boundary arrow and one full finite endpoint source construct an
arrow over the entire valuation ring. Both prescribed endpoints and the full
original boundary ideal are retained; no radical or reduced boundary is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [A.IsSeparated]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
  {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
local notation "η" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "pJ" => pullback.snd p J.subschemeι
local notation "qJ" => InvariantIdealRelation.snd J p q hJ

include e

/-- Extend an actual boundary arrow, constructing full finiteness at both unchanged endpoints. -/
theorem originalBoundary_valuation_arrow_of_finite_endpoint
    (x y : Spec (.of R) ⟶ J.subscheme)
    (hf : IsFinite (pullback.snd p (x ≫ J.subschemeι)) ∨
      IsFinite (pullback.snd p (y ≫ J.subschemeι)))
    (d : Spec (.of K) ⟶ pullback p J.subschemeι)
    (hx : d ≫ pJ = η ≫ x) (hy : d ≫ qJ = η ≫ y) :
    ∃ a : Spec (.of R) ⟶ pullback p J.subschemeι,
      η ≫ a = d ∧ a ≫ pJ = x ∧ a ≫ qJ = y ∧
      IsFinite (pullback.snd p (x ≫ J.subschemeι)) ∧
      IsFinite (pullback.snd p (y ≫ J.subschemeι)) := by
  have hx' : (d ≫ pullback.fst p J.subschemeι) ≫ p = η ≫ (x ≫ J.subschemeι) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.assoc]
  have hy' : (d ≫ pullback.fst p J.subschemeι) ≫ q = η ≫ (y ≫ J.subschemeι) := by
    rw [Category.assoc, ← InvariantIdealRelation.snd_ι J p q hJ,
      ← Category.assoc, hy, Category.assoc]
  obtain ⟨a, ha, hap, haq, hfx, hfy⟩ :=
    EquivalenceRelationFiber.valuation_arrow_of_finite_endpoint e
      (x ≫ J.subschemeι) (y ≫ J.subschemeι) hf (d ≫ pullback.fst p J.subschemeι) hx' hy'
  refine ⟨pullback.lift a x hap, ?_, pullback.lift_snd _ _ _, ?_, hfx, hfy⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ha]
    · rw [Category.assoc, pullback.lift_snd, hx]
  · apply (cancel_mono J.subschemeι).mp
    rw [Category.assoc, InvariantIdealRelation.snd_ι, pullback.lift_fst_assoc, haq]

omit [A.IsSeparated] [IsDomain R] [ValuationRing R] in
/-- The full boundary extension is unique, including both original endpoint equations. -/
theorem originalBoundary_valuation_arrow_unique (x y : Spec (.of R) ⟶ J.subscheme)
    {a b : Spec (.of R) ⟶ pullback p J.subschemeι}
    (ha : a ≫ pJ = x) (ha' : a ≫ qJ = y)
    (hb : b ≫ pJ = x) (hb' : b ≫ qJ = y) : a = b := by
  apply pullback.hom_ext
  · apply e.right_cancellation
    · rw [Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc, ← Category.assoc, ha, hb]
    · rw [Category.assoc, Category.assoc, ← InvariantIdealRelation.snd_ι J p q hJ,
        ← Category.assoc, ← Category.assoc, ha', hb']
  · exact ha.trans hb.symm

end FLT.Mazur.EquivalenceRelationOrderedFrames
