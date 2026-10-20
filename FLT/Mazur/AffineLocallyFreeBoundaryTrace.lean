/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeRelationTrace
public import FLT.Mazur.AffineTraceLinearity
public import FLT.Mazur.SchemeRelationInvariantFunctorial
public import FLT.Mazur.SectionLiftIdeal

/-!
# Weighted trace lifts across a full cartesian boundary relation

A lift of a boundary invariant need not be invariant. Its weighted relation
trace is invariant and lifts the trace multiple. This uses the entire original
relation, with arbitrary local ranks and no division by a degree.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineLocallyFreeRelationTrace
open AffineTraceGluing AffineNormCartesianGluing SchemeEffectiveEpiSections
open SchemeRelationInvariantSpectrum
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  {ι : Type v} (U : ι → A.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis p (U i)) (hcover : ⨆ i, (U i).1 = ⊤)
  (e : CategoryTheory.EquivalenceRelation p q)

/-- The trace as an element of the unchanged full invariant ring. -/
def invariantTrace (s : Γ(A, ⊤)) : compatibleFunctions p q :=
  ⟨relationTrace p q U hU hcover s, relationTrace_invariant p q U hU hcover e s⟩

/-- Invariant scalars can be taken outside the full relation trace. -/
theorem invariantTrace_mul (r : compatibleFunctions p q) (s : Γ(A, ⊤)) :
    invariantTrace p q U hU hcover e (r.val * s) =
      r * invariantTrace p q U hU hcover e s := by
  apply Subtype.ext
  change trace p U hU hcover (q.appTop (r.val * s)) =
    r.val * trace p U hU hcover (q.appTop s)
  rw [map_mul, ← r.property, trace_mul]

variable {D' A' : Scheme.{u}} [IsAffine D'] [IsAffine A']
  (p' q' : D' ⟶ A') (u : A' ⟶ A) (v : D' ⟶ D)
  (H : IsPullback v p' p u) (hq : v ≫ q = q' ≫ u)
local notation "φ" => relationPullback p q p' q' u v H.w hq

/-- A weighted trace is an actual original invariant lift of a boundary trace multiple. -/
theorem boundary_weightedTrace (t : compatibleFunctions p' q')
    (b : Γ(A, ⊤)) (hb : u.appTop b = t.val) (a : Γ(A, ⊤)) :
    φ (invariantTrace p q U hU hcover e (a * b)) =
      φ (invariantTrace p q U hU hcover e a) * t := by
  apply Subtype.ext
  change u.appTop (trace p U hU hcover (q.appTop (a * b))) =
    u.appTop (trace p U hU hcover (q.appTop a)) * t.val
  rw [← trace_pullback H U hU hcover, ← trace_pullback H U hU hcover]
  have hv (s : Γ(A, ⊤)) : v.appTop (q.appTop s) = q'.appTop (u.appTop s) :=
    congrArg (fun k : D' ⟶ A ↦ k.appTop s) hq
  rw [hv, hv, map_mul, hb, map_mul, ← t.property, mul_comm,
    trace_mul, mul_comm]

/-- Surjective ambient restriction supplies the weighted lift for every boundary invariant. -/
theorem invariantTrace_mem_sectionLiftIdeal (hs : Function.Surjective u.appTop)
    (t : compatibleFunctions p' q') (a : Γ(A, ⊤)) :
    invariantTrace p q U hU hcover e a ∈ sectionLiftIdeal φ t := by
  obtain ⟨b, hb⟩ := hs t.val
  exact ⟨invariantTrace p q U hU hcover e (a * b),
    boundary_weightedTrace p q U hU hcover e p' q' u v H hq t b hb a⟩

/-- The constructed relation degree is a lifting multiplier for every boundary invariant. -/
theorem traceDegree_mem_sectionLiftIdeal (hs : Function.Surjective u.appTop)
    (t : compatibleFunctions p' q') :
    invariantTrace p q U hU hcover e 1 ∈ sectionLiftIdeal φ t :=
  invariantTrace_mem_sectionLiftIdeal p q U hU hcover e p' q' u v H hq hs t 1

end FLT.Mazur.AffineLocallyFreeRelationTrace
