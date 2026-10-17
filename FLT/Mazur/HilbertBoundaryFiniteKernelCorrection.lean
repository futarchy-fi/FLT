/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryAmbientFrame
public import FLT.Mazur.FiniteKernelCorrections

/-!
# Exact invariant lifts in the constructed boundary kernel coordinates

The actual geometric finite kernel frame parametrizes all possible corrections
of a chosen ambient boundary lift. Vanishing is one equation on the entire
original relation. No local solution of that equation is assumed or asserted.
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

/-- All ambient lifts of an original boundary section have the constructed finite coordinates. -/
theorem originalAmbientBoundaryLift_coordinates (t : D₀) (b : Q) :
    r₀ b = (invariantInclusion ec).hom.app (op Wc) t ↔
      ∃ u : Fin n → Q, b = originalAmbientBoundaryLift f hL d V c k W hW t +
        ∑ j, u j * v j := by
  rw [← originalAmbientBoundaryLift_restrict f hL d V c k W hW t]
  exact FiniteKernelCorrections.same_image_iff r₀ v
    (originalAmbientBoundaryFrame_span f hL d V c k W hW) _ b

/-- Any ambient lift yields the exact finite correction test for invariant lifting. -/
theorem originalBoundary_lift_iff_finite_correction (t : D₀) (a : Q)
    (ha : r₀ a = (invariantInclusion ec).hom.app (op Wc) t) :
    (∃ b : (invariantSheaf e).obj.obj (op W), ρ b = t) ↔
      ∃ u : Fin n → Q, p₀ a - q₀ a +
        ∑ j, (p₀ (u j) * p₀ (v j) - q₀ (u j) * q₀ (v j)) = 0 := by
  have h : (∃ b : (invariantSheaf e).obj.obj (op W), ρ b = t) ↔
      ∃ b : Q, r₀ b = (invariantInclusion ec).hom.app (op Wc) t ∧
        relationDifference e W b = 0 := by
    unfold originalAmbientBoundaryRestriction originalClosedSectionPullback
    exact invariantMap_section_lift_iff e ec (i).left (z).left
      (originalClosedArrow_left_fst f hL d V c k)
      (originalClosedArrow_left_snd f hL d V c k) W t
  rw [h]
  simp only [relationDifference_eq_zero]
  rw [← ha]
  exact FiniteKernelCorrections.invariant_lift_iff r₀ v
    (originalAmbientBoundaryFrame_span f hL d V c k W hW) p₀ q₀ a

/-- The constructed lift and frame give an unconditional exact finite test. -/
theorem originalBoundary_lift_iff_chosen_finite_correction (t : D₀) :
    (∃ b : (invariantSheaf e).obj.obj (op W), ρ b = t) ↔
      ∃ u : Fin n → Q,
        p₀ (originalAmbientBoundaryLift f hL d V c k W hW t) -
          q₀ (originalAmbientBoundaryLift f hL d V c k W hW t) +
            ∑ j, (p₀ (u j) * p₀ (v j) - q₀ (u j) * q₀ (v j)) = 0 :=
  originalBoundary_lift_iff_finite_correction f hL d V c k W hW t _
    (originalAmbientBoundaryLift_restrict f hL d V c k W hW t)

end FLT.Mazur.HilbertChart.AffineRestriction
