/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteDomainErrorVanishing
public import FLT.Mazur.HilbertFiniteAffineNeighborhood

/-!
# Original local errors vanish on constructed finite-locus neighborhoods

A single finite-locus source point now constructs the affine invariant domain
needed by the original error theorem. No affine neighborhood or principal
coverage witness is requested from the caller. The error remains the original
boundary error on this constructed neighborhood, not on the larger ambient open.
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
open OrbitBoundaryAtlas.FiniteAtlas
variable [IsAffine V.left]
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
  EquivalenceRelationNormalizedFrames.source invariantSheaf sourceSheaf
  originalBoundaryLiftErrorClass originalBoundaryExtendedCokernelAddCommGroup
  originalBoundaryExtendedCokernelModule
attribute [local instance] originalBoundarySectionAlgebra originalAmbientSourceAlgebra
  originalAmbientRelationAlgebra originalAmbientBoundaryAlgebra

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
  (x : A.left) (hx : projection (equivalence f hL d V c k) x ∈ W)
  (hf : x ∈ finiteTargetOpen (Over.Hom.left (fst f hL d V c k)))
local notation "Z" => originalFiniteAffineNeighborhood f hL d V c k W x hx hf
local notation "ha" => originalFiniteAffineNeighborhood_affine f hL d V c k W x hx hf
local notation "Zc" => (TopologicalSpace.Opens.map (m).base).obj Z
local notation "T" => (sourceSheaf ec).obj.obj (op Zc)
local notation "D₀" => (invariantSheaf ec).obj.obj (op Zc)
local notation "κ" =>
  (((invariantInclusion ec).hom.app (op Zc)).hom).comp
    (originalClosedSectionPullback f hL d V c k Z)

/-- Every original source-prime error vanishes on the neighborhood constructed from the point. -/
theorem originalSourceError_zero_on_finiteNeighborhood (P : Ideal T) [P.IsPrime] (t : D₀) :
    originalBoundaryLiftErrorClass f hL d V c k Z ha
      (Localization.AtPrime (P.comap κ)) t = 0 :=
  originalSourceError_zero_of_finiteDomain f hL d V c k Z ha
    (originalFiniteAffineNeighborhood_finite f hL d V c k W x hx hf) P t

/-- The constructed finite-locus neighborhood has complete original principal-core coverage. -/
theorem originalFiniteNeighborhood_principalCore :
    OrbitBoundaryAtlas.uniformPrincipalCore f hL d V c k Z = Z :=
  OrbitBoundaryAtlas.uniformPrincipalCore_eq_of_finiteDomain f hL d V c k Z
    (originalFiniteAffineNeighborhood_finite f hL d V c k W x hx hf) ha

/-- Every boundary section has full original power-lifting locus on the constructed domain. -/
theorem originalFiniteNeighborhood_liftOpen (t : D₀) :
    originalBoundaryLiftOpen f hL d V c k Z t = Z :=
  originalBoundaryLiftOpen_eq_of_finiteDomain f hL d V c k Z ha
    (originalFiniteAffineNeighborhood_finite f hL d V c k W x hx hf) t

end FLT.Mazur.HilbertChart.AffineRestriction
