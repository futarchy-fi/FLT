/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteFreeRelationPrincipalCoverage

/-!
# Original local scalar error vanishing for finite-free original relations

The constructed whole-relation norms cover the original boundary source.
Consequently every prime avoids the actual geometric scalar ideal, and every
fixed-domain error vanishes after the prescribed original localization.
The finite basis is still an input on the full original first projection.
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
attribute [local irreducible] originalBoundaryLiftErrorClass invariantSheaf sourceSheaf
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

local notation "S" => OrbitBoundaryAtlas.uniformPrincipalScalars f hL d V c k W
local notation "J" => OrbitBoundaryAtlas.uniformPrincipalIdeal f hL d V c k W

variable [IsAffine (relation f hL d V c k).left] {ι : Type} [Finite ι]

/-- Whole-relation principal coverage kills every original error at every source prime. -/
theorem originalSourceError_zero_of_relationBasis (P : Ideal T) [P.IsPrime] (t : D₀) :
    let _ := (p).left.appTop.hom.toAlgebra
    ∀ (_basis : Module.Basis ι Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤)),
      originalBoundaryLiftErrorClass f hL d V c k W hW
        (Localization.AtPrime (P.comap κ)) t = 0 := by
  let _ := (p).left.appTop.hom.toAlgebra
  dsimp only
  intro basis
  apply uniformPrincipalBoundaryIdeal_error_zero f hL d V c k W hW P
  rw [OrbitBoundaryAtlas.uniformPrincipalBoundaryIdeal_eq_top_of_basis
    f hL d V c k W hW basis]
  intro h
  exact Ideal.IsPrime.ne_top ‹P.IsPrime› (top_unique h)

include hW in
/-- Every original boundary section has a fixed-domain power lift locally on the whole domain. -/
theorem originalBoundaryLiftOpen_eq_of_relationBasis (t : D₀) :
    let _ := (p).left.appTop.hom.toAlgebra
    ∀ (_basis : Module.Basis ι Γ(A.left, ⊤) Γ((relation f hL d V c k).left, ⊤)),
      originalBoundaryLiftOpen f hL d V c k W t = W := by
  let _ := (p).left.appTop.hom.toAlgebra
  dsimp only
  intro basis
  apply le_antisymm (principalLiftOpen_le e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W t)
  exact (OrbitBoundaryAtlas.uniformPrincipalCore_eq_of_basis f hL d V c k W basis).ge.trans
    (OrbitBoundaryAtlas.uniformPrincipalCore_le_boundaryLiftOpen f hL d V c k W hW t)

end FLT.Mazur.HilbertChart.AffineRestriction
