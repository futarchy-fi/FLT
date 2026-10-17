/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryPrimeKernelCorrection
public import FLT.Mazur.HilbertBoundaryLocalizedKernelOperator
public import FLT.Mazur.HilbertBoundaryKernelCorrectionNumerator

/-!
# Original source prime errors and localized kernel solutions

At a boundary source prime, the full local scalar error is zero precisely
when the localized actual kernel operator corrects the ambient lift defect.
A solution constructs an original multiplier outside the prime and an exact
invariant numerator with its finite ambient coordinate formula retained.
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

attribute [local instance] originalAmbientSourceAlgebra originalAmbientRelationAlgebra
  originalAmbientBoundaryAlgebra
attribute [local irreducible] relationSheaf originalAmbientLocalizedCorrection

/-- The actual source-prime error is exactly the localized full kernel correction problem. -/
theorem originalBoundarySourceError_eq_zero_iff_localized_kernel [IsAffine V.left]
    (P : Ideal T) [P.IsPrime] (t : D₀) :
    originalBoundaryLiftErrorClass f hL d V c k W hW
        (Localization.AtPrime (P.comap κ)) t = 0 ↔
      ∃ w, LocalizedModule.mk
          (p₀ (originalAmbientBoundaryLift f hL d V c k W hW t) -
            q₀ (originalAmbientBoundaryLift f hL d V c k W hW t))
          (1 : (P.comap κ).primeCompl) +
        originalAmbientLocalizedCorrection f hL d V c k W hW (P.comap κ).primeCompl w = 0 := by
  rw [originalBoundarySourceError_eq_zero_iff_kernel_correction,
    originalAmbientLocalizedCorrection_iff]
  constructor
  · rintro ⟨a, ha, u, hu⟩
    exact ⟨⟨a, ha⟩, u, hu⟩
  · rintro ⟨a, u, hu⟩
    exact ⟨a.val, a.property, u, hu⟩

/-- Clearing a localized solution returns its original invariant numerator and ambient formula. -/
theorem originalBoundaryPrimeLocalizedCorrection_numerator
    (P : Ideal T) [P.IsPrime] (t : D₀)
    (h : ∃ w, LocalizedModule.mk
        (p₀ (originalAmbientBoundaryLift f hL d V c k W hW t) -
          q₀ (originalAmbientBoundaryLift f hL d V c k W hW t))
        (1 : (P.comap κ).primeCompl) +
      originalAmbientLocalizedCorrection f hL d V c k W hW (P.comap κ).primeCompl w = 0) :
    ∃ a : Ω, κ a ∉ P ∧ ∃ (u : Fin n → Q) (b : Ω),
      ι₀ b = ι₀ a * originalAmbientBoundaryLift f hL d V c k W hW t + ∑ j, u j * v j ∧
      ρ b = ρ a * t := by
  obtain ⟨a, u, hu⟩ :=
    (originalAmbientLocalizedCorrection_iff f hL d V c k W hW (P.comap κ).primeCompl _).mp h
  obtain ⟨b, hb, _⟩ := originalBoundaryKernelCorrection_numerator f hL d V c k W hW t a.val u hu
  exact ⟨a.val, a.property, u, b, hb⟩

end FLT.Mazur.HilbertChart.AffineRestriction
