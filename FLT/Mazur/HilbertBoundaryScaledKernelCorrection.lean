/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryFiniteKernelCorrection

/-!
# Original scalar multipliers in the finite boundary correction equation

An invariant multiplier scales the defect of a chosen original ambient lift.
The same geometric kernel frame supplies all corrections. Solving the equation
returns an exact original invariant numerator, without any residual test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

open RelativeRelationOrbit
local notation "e" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence

local notation "m" => originalClosedInvariantMap f hL d V c k

set_option quotPrecheck false
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Q" => (sourceSheaf e).obj.obj (op W)
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)

local notation "D₀" => (invariantSheaf ec).obj.obj (op Wc)
local notation "r₀" => originalAmbientBoundaryRestriction f hL d V c k W
attribute [local irreducible] originalAmbientBoundaryRestriction
variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)

local notation "v" => originalAmbientBoundaryFrame f hL d V c k W hW
local notation "n" => originalAmbientBoundaryFrameSize f hL d V c k W hW
local notation "p₀" => ((firstRestriction e).hom.app (op W)).hom
local notation "q₀" => ((secondRestriction e).hom.app (op W)).hom
local notation "ρ" => originalClosedSectionPullback f hL d V c k W
attribute [local irreducible] originalAmbientBoundaryFrame originalAmbientBoundaryFrameSize
  originalAmbientBoundaryLift

local notation "ι₀" => ((invariantInclusion e).hom.app (op W)).hom
local notation "ιc" => ((invariantInclusion ec).hom.app (op Wc)).hom

/-- Multiplying an ambient lift by an original invariant scalar preserves exact restriction. -/
theorem originalAmbientBoundaryLift_scaled_restrict (t : D₀)
    (aScalar : (invariantSheaf e).obj.obj (op W)) :
    r₀ (ι₀ aScalar * originalAmbientBoundaryLift f hL d V c k W hW t) = ιc (ρ aScalar * t) := by
  rw [map_mul, originalAmbientBoundaryRestriction_invariant,
    originalAmbientBoundaryLift_restrict, map_mul]

/-- The full relation defect scales through either endpoint of an invariant scalar. -/
theorem originalAmbientBoundaryLift_scaled_difference (t : D₀)
    (aScalar : (invariantSheaf e).obj.obj (op W)) :
    p₀ (ι₀ aScalar * originalAmbientBoundaryLift f hL d V c k W hW t) -
        q₀ (ι₀ aScalar * originalAmbientBoundaryLift f hL d V c k W hW t) =
      p₀ (ι₀ aScalar) * (p₀ (originalAmbientBoundaryLift f hL d V c k W hW t) -
        q₀ (originalAmbientBoundaryLift f hL d V c k W hW t)) := by
  have hs : p₀ (ι₀ aScalar) = q₀ (ι₀ aScalar) := invariantSection_condition e W aScalar
  simp only [map_mul, ← hs, mul_sub]

/-- Exact original scaled numerators are equivalent to the finite ambient correction equation. -/
theorem originalBoundary_scaled_lift_iff_finite_correction (t : D₀)
    (aScalar : (invariantSheaf e).obj.obj (op W)) :
    (∃ b : (invariantSheaf e).obj.obj (op W), ρ b = ρ aScalar * t) ↔
      ∃ u : Fin n → Q,
        p₀ (ι₀ aScalar) * (p₀ (originalAmbientBoundaryLift f hL d V c k W hW t) -
          q₀ (originalAmbientBoundaryLift f hL d V c k W hW t)) +
            ∑ j, (p₀ (u j) * p₀ (v j) - q₀ (u j) * q₀ (v j)) = 0 := by
  rw [originalBoundary_lift_iff_finite_correction f hL d V c k W hW (ρ aScalar * t) _
    (originalAmbientBoundaryLift_scaled_restrict f hL d V c k W hW t aScalar),
    originalAmbientBoundaryLift_scaled_difference]

end FLT.Mazur.HilbertChart.AffineRestriction
