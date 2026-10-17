/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryPrimeLocalizedCorrection
public import FLT.Mazur.HilbertUniformPrincipalScalarIdeal

/-!
# Uniform geometric principal neighborhoods solve original prime corrections

An original invariant scalar whose principal open lies in a uniform chart
image produces a genuine localized correction at every source prime where
that scalar is nonzero. The scalar and its neighborhood are explicit inputs;
coverage of all original primes is not asserted.
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
attribute [local irreducible] originalBoundaryLiftErrorClass sourceSheaf
  originalBoundaryExtendedCokernelAddCommGroup originalBoundaryExtendedCokernelModule
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
local notation "κ" => (ιc).comp ρ

attribute [local instance] originalAmbientSourceAlgebra originalAmbientRelationAlgebra
  originalAmbientBoundaryAlgebra
attribute [local irreducible] relationSheaf originalAmbientLocalizedCorrection

variable [IsAffine V.left]
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
  EquivalenceRelationNormalizedFrames.source
  OrbitBoundaryAtlas.uniformPrincipalScalars

/-- A geometric scalar kills every fixed-domain error at each source prime avoiding it. -/
theorem uniformScalar_originalSourceError_zero (a : Ω)
    (ha : a ∈ OrbitBoundaryAtlas.uniformPrincipalScalars f hL d V c k W)
    (P : Ideal T) [P.IsPrime] (hP : κ a ∉ P) (t : D₀) :
    originalBoundaryLiftErrorClass f hL d V c k W hW
      (Localization.AtPrime (P.comap κ)) t = 0 := by
  obtain ⟨N, b, hb⟩ :=
    OrbitBoundaryAtlas.uniformPrincipalScalars_power_lift f hL d V c k W hW a ha t
  apply (originalBoundarySourceError_eq_zero_iff f hL d V c k W hW P t).mpr
  refine ⟨a ^ N, ?_, b, ?_⟩
  · rw [map_pow]
    exact fun h ↦ hP ((inferInstance : P.IsPrime).mem_of_pow_mem N h)
  · change ρ b = ρ (a ^ N) * t
    rw [map_pow]
    exact hb

/-- The geometric multiplier supplies an actual solution of the localized kernel equation. -/
theorem uniformScalar_originalLocalizedCorrection (a : Ω)
    (ha : a ∈ OrbitBoundaryAtlas.uniformPrincipalScalars f hL d V c k W)
    (P : Ideal T) [P.IsPrime] (hP : κ a ∉ P) (t : D₀) :
    ∃ w, LocalizedModule.mk
        (p₀ (originalAmbientBoundaryLift f hL d V c k W hW t) -
          q₀ (originalAmbientBoundaryLift f hL d V c k W hW t))
        (1 : (P.comap κ).primeCompl) +
      originalAmbientLocalizedCorrection f hL d V c k W hW (P.comap κ).primeCompl w = 0 :=
  (originalBoundarySourceError_eq_zero_iff_localized_kernel f hL d V c k W hW P t).mp
    (uniformScalar_originalSourceError_zero f hL d V c k W hW a ha P hP t)

end FLT.Mazur.HilbertChart.AffineRestriction
