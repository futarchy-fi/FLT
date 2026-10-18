/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceConstructedOpenLifts

/-!
# Geometric original-prime tests for the constructed Hilbert source open

Complete source fibers lie in the proven uniform good relation open.
Closedness of its original scalar bad image, or local integrality of an
affine bad quotient, supplies prime avoidance. The boundary sections and
full relation equations are already constructed, not additional inputs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
local notation "hr" => originalClosedFst_isPullback f hL d V c k
local notation "hs" => congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
local notation "m" => originalClosedInvariantMap f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedOriginalBoundaryAction f hL d V c k n o
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
local notation "j" => normalizedOriginalBoundaryInclusion f hL d V c k n o
local notation "b" => normalizedOriginalBoundaryEndpoint f hL d V c k n o
local notation "hj" => normalizedOriginalBoundaryAction_inclusion f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Uc" => (pullOpen ec Wc).val
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)

local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)
local notation "E" => (pullOpen eo W).val

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS
local notation "τU" => restrictedAction τ U hU
local notation "jU" => j ∣_ U
local notation "σ" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σ₀" => invariantScalarCoordinates τU σ
local notation "Tsource" => (sourceSheaf ec).obj.obj (op Wc)
local notation "κ" => ((invariantInclusion ec).hom.app (op Wc)).hom.comp
  (originalClosedSectionPullback f hL d V c k W)

attribute [local irreducible] normalizedOriginalScalarMap
  SchemeRelationRestriction.doubleDomain SchemeRelationRestriction.fst
  SchemeRelationRestriction.snd SchemeRelationRestriction.arrow

local notation "Bsource" => invariantCoordinates (boundaryOpenAction ρ τ j hj U hU)
local notation "α" => normalizedOriginalBoundaryHom f hL d V c k n o W U hU hUW

attribute [local irreducible] normalizedOriginalBoundary
  normalizedOriginalBoundaryInclusion normalizedOriginalBoundaryAction
  normalizedFullRelationAction
  originalSourceCompatibleModule

local notation "Csource" => originalSourceCompatibleModule f hL d V c k n o W U hU hUW
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

attribute [local irreducible] OriginalPrimeIntegralFiber.localizedMap
  invariantSheaf sourceSheaf invariantInclusion originalClosedSectionPullback
  invariantScalarCoordinates

open SchemeScalarPrincipalNeighborhood
local notation "Lgood" => originalSourceGoodRelationOpen f hL d V c k n o U hU
local notation "Ogood" => originalSourceConstructedOpen f hL d V c k n o U hU
local notation "σR" => (F).appTop.hom.comp σ₀


/-- Completeness of every original scalar source point puts its whole relation fiber in the open. -/
theorem originalSourceGoodRelationOpen_scalar_fiber (P : Ideal Tsource) [P.IsPrime]
    (hP : ∀ x : U.toScheme, scalarMorphism σ₀ x = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
      U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    ∀ xR : D, scalarMorphism σR xR = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
      xR ∈ Lgood := by
  intro xR hz
  apply originalSourceGoodRelationOpen_contains f hL d V c k n o U hU
  apply hP (F xR)
  rw [scalarMorphism_comp] at hz
  exact hz

/-- Closedness only of the bad relation image supplies an original safe prime. -/
theorem originalSourceConstructedOpen_safe_of_complete_fiber
    (P : Ideal Tsource) [P.IsPrime]
    (hc : IsClosed (scalarMorphism σR '' (Lgood : Set D)ᶜ))
    (hP : ∀ x : U.toScheme, scalarMorphism σ₀ x = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
      U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    (PrimeSpectrum.comap κ ⟨P, inferInstance⟩) ∈ scalarNeighborhoodLocus σR Lgood := by
  apply (SchemeWholeFiberOpen.mem_locus_iff_of_badImage_closed
    (scalarMorphism σR) Lgood hc (PrimeSpectrum.comap κ ⟨P, inferInstance⟩)).mpr
  exact originalSourceGoodRelationOpen_scalar_fiber f hL d V c k n o W U hU hUW P hP

/-- Where the relation is affine, its bad quotient only needs integrality at the original prime. -/
theorem originalSourceConstructedOpen_safe_of_complete_badQuotient
    (P : Ideal Tsource) [P.IsPrime]
    [IsAffine (SchemeRelationRestriction.doubleDomain p q kS)]
    (J : Ideal Γ(D, ⊤))
    (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(D, ⊤)) =
      (D).toSpecΓ '' (Lgood : Set D)ᶜ)
    (hInt : (OriginalPrimeIntegralFiber.localizedMap
      ((Ideal.Quotient.mk J).comp σR)
      (PrimeSpectrum.comap κ ⟨P, inferInstance⟩).asIdeal).IsIntegral)
    (hP : ∀ x : U.toScheme, scalarMorphism σ₀ x = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
      U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    (PrimeSpectrum.comap κ ⟨P, inferInstance⟩) ∈ scalarNeighborhoodLocus σR Lgood :=
  mem_scalarNeighborhoodLocus_of_badQuotient_local_integral σR J Lgood hJ
    (PrimeSpectrum.comap κ ⟨P, inferInstance⟩) hInt
    (originalSourceGoodRelationOpen_scalar_fiber f hL d V c k n o W U hU hUW P hP)

/-- A complete original source fiber and closed bad relation image give full localized lifting. -/
theorem originalSource_surjective_of_complete_fiber (ha : IsAffineOpen U)
    (P : Ideal Tsource) [P.IsPrime]
    (hc : IsClosed (scalarMorphism σR '' (Lgood : Set D)ᶜ))
    (hP : ∀ x : U.toScheme, scalarMorphism σ₀ x = PrimeSpectrum.comap κ ⟨P, inferInstance⟩ →
      U.ι x ∈ completePointLocus («p» := p) («q» := q) (Fin n) o) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) :=
  originalSource_constructedOpen_surjective f hL d V c k n o W U hU hUW ha P
    (originalSourceConstructedOpen_safe_of_complete_fiber
      f hL d V c k n o W U hU hUW P hc hP)

end FLT.Mazur.HilbertChart.AffineRestriction
