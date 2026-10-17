/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryScaledKernelCorrection

/-!
# Constructing the original invariant numerator of a kernel correction

A solved finite equation constructs a unique invariant section whose ambient
regular function is exactly the scaled chosen lift plus the supplied kernel
combination. Its boundary restriction is the prescribed scaled section.
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

local notation "Ω" => (invariantSheaf e).obj.obj (op W)

/-- The corrected ambient function restricts exactly to the required boundary numerator. -/
theorem originalAmbientCorrectedLift_restrict (t : D₀) (a : Ω) (u : Fin n → Q) :
    r₀ (ι₀ a * originalAmbientBoundaryLift f hL d V c k W hW t + ∑ j, u j * v j) =
      ιc (ρ a * t) := by
  rw [map_add, originalAmbientBoundaryLift_scaled_restrict,
    FiniteKernelCorrections.sum_restrict r₀ v
      (originalAmbientBoundaryFrame_span f hL d V c k W hW), add_zero]

/-- A solved full relation equation constructs the unique original invariant numerator. -/
theorem originalBoundaryKernelCorrection_numerator (t : D₀) (a : Ω) (u : Fin n → Q)
    (hu : p₀ (ι₀ a) * (p₀ (originalAmbientBoundaryLift f hL d V c k W hW t) -
        q₀ (originalAmbientBoundaryLift f hL d V c k W hW t)) +
      ∑ j, (p₀ (u j) * p₀ (v j) - q₀ (u j) * q₀ (v j)) = 0) :
    ∃! b : Ω, ι₀ b =
      ι₀ a * originalAmbientBoundaryLift f hL d V c k W hW t + ∑ j, u j * v j ∧
      ρ b = ρ a * t := by
  let x := ι₀ a * originalAmbientBoundaryLift f hL d V c k W hW t + ∑ j, u j * v j
  have hx : p₀ x = q₀ x := by
    apply sub_eq_zero.mp
    change p₀ (_ + _) - q₀ (_ + _) = 0
    rw [map_add, map_add]
    have he := originalAmbientBoundaryLift_scaled_difference f hL d V c k W hW t a
    have hc := FiniteKernelCorrections.difference_sum v p₀ q₀ u
    linear_combination he + hc + hu
  obtain ⟨b, hb, huniq⟩ := invariantSection_existsUnique e W x hx
  have hρ : ρ b = ρ a * t := by
    apply invariantSection_ext ec Wc
    change ιc (ρ b) = ιc (ρ a * t)
    rw [← originalAmbientBoundaryRestriction_invariant, hb]
    exact originalAmbientCorrectedLift_restrict f hL d V c k W hW t a u
  exact ⟨b, ⟨hb, hρ⟩, fun b' hb' ↦ huniq b' hb'.1⟩

end FLT.Mazur.HilbertChart.AffineRestriction
