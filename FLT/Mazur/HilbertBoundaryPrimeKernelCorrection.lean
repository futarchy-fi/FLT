/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryScaledKernelCorrection
public import FLT.Mazur.HilbertOrbitBoundarySourceErrorCriterion

/-!
# Actual source prime errors in finite geometric kernel coordinates

At an original boundary source prime, the scalar error vanishes exactly when
one original multiplier outside that prime and a finite tuple of ambient
coefficients solve the full relation correction equation. The finite kernel
frame and ambient lift are constructed from the original Hilbert geometry.
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

open OrbitBoundaryAtlas.FiniteAtlas
attribute [local instance] originalBoundarySectionAlgebra
attribute [local irreducible] originalBoundaryLiftErrorClass invariantSheaf sourceSheaf
  originalBoundaryExtendedCokernelAddCommGroup originalBoundaryExtendedCokernelModule
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "κ" => (ιc).comp ρ
variable [IsAffine V.left]

/-- The local scalar obstruction has an exact test using the constructed finite ambient frame. -/
theorem originalBoundarySourceError_eq_zero_iff_kernel_correction
    (P : Ideal T) [P.IsPrime] (t : D₀) :
    originalBoundaryLiftErrorClass f hL d V c k W hW
        (Localization.AtPrime (P.comap κ)) t = 0 ↔
      ∃ aScalar : Ω, κ aScalar ∉ P ∧ ∃ u : Fin n → Q,
        p₀ (ι₀ aScalar) * (p₀ (originalAmbientBoundaryLift f hL d V c k W hW t) -
          q₀ (originalAmbientBoundaryLift f hL d V c k W hW t)) +
            ∑ j, (p₀ (u j) * p₀ (v j) - q₀ (u j) * q₀ (v j)) = 0 := by
  rw [originalBoundarySourceError_eq_zero_iff f hL d V c k W hW P t]
  apply exists_congr
  intro aScalar
  apply and_congr_right
  intro _
  change (∃ b : Ω, ρ b = ρ aScalar * t) ↔ _
  exact originalBoundary_scaled_lift_iff_finite_correction f hL d V c k W hW t aScalar

end FLT.Mazur.HilbertChart.AffineRestriction
