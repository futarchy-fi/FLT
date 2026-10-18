/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceGeneratedLocalizedSurjectivity
public import FLT.Mazur.HilbertSourceBadQuotientLifts
public import FLT.Mazur.OriginalScalarLocalizedSurjectivity

/-!
# Full source surjectivity from coefficientwise usable opens

Every boundary coefficient may choose its own open and original denominator.
No finite generation of the invariant boundary module is required. Local
bad-quotient tests supply avoidance on each such open, retaining the full
source relation and the original boundary prime.
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
  normalizedFullRelationFrames normalizedFullRelationAction
  originalSourceCompatibleModule

local notation "Csource" => originalSourceCompatibleModule f hL d V c k n o W U hU hUW
local notation "βsource" => originalSourceCompatibleBoundaryMap f hL d V c k n o W U hU hUW

attribute [local irreducible] OriginalPrimeIntegralFiber.localizedMap
  invariantSheaf sourceSheaf invariantInclusion originalClosedSectionPullback
  invariantScalarCoordinates

/-- Full source localized surjectivity is exactly coefficientwise original numerator lifting. -/
theorem originalSourceCompatible_surjective_iff_numerators
    (P : Ideal Tsource) [P.IsPrime] :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) ↔
      ∀ t : Bsource, ∃ x₀ : Ω, κ x₀ ∉ P ∧ ∃ w : Sinv,
        normalizedBoundaryChartMap f hL d V c k n o U hU w =
          normalizedBoundaryChartMap f hL d V c k n o U hU (σ x₀) * t ∧
        w.val ∈ SchemeEffectiveEpiSections.compatibleFunctions F H := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  change Function.Surjective (LocalizedModule.map
    (originalSubframePrimeDenominators f hL d V c k W P)
    ((α).toLinearMap.comp (Csource).subtype)) ↔ _
  rw [OriginalScalarLocalizedSurjectivity.compatible_surjective_iff]
  constructor
  · intro h t
    obtain ⟨x, w, hw, hb⟩ := h t
    exact ⟨x.val, x.property, w, hb,
      (mem_originalSourceCompatibleModule f hL d V c k n o W U hU hUW w).mp hw⟩
  · intro h t
    obtain ⟨x, hx, w, hb, hw⟩ := h t
    exact ⟨⟨x, hx⟩, w,
      (mem_originalSourceCompatibleModule f hL d V c k n o W U hU hUW w).mpr hw, hb⟩

variable (ha : IsAffineOpen U)

include ha in
/-- Independent usable opens for all coefficients suffice without boundary finiteness. -/
theorem originalSource_coefficientwise_pairOpen_surjective
    (P : Ideal Tsource) [P.IsPrime]
    (h : ∀ t : Bsource, ∃ (O : U.toScheme.Opens)
      (hO : ∀ g : Equiv.Perm (Fin n), (τU g).hom ⁻¹ᵁ O = O),
      PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈
        SchemeScalarPrincipalNeighborhood.scalarNeighborhoodLocus σ₀ O ∧
      ∃ v : invariantCoordinates (restrictedAction τU O hO),
        ((jU) ∣_ O).appTop v.val = ((jU) ⁻¹ᵁ O).ι.appTop t.val ∧
        (pairOpenFirst O F H).appTop v.val = (pairOpenSecond O F H).appTop v.val) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  apply (originalSourceCompatible_surjective_iff_numerators
    f hL d V c k n o W U hU hUW P).mpr
  intro t
  obtain ⟨O, hO, hSafe, v, hb, he⟩ := h t
  exact originalSource_pairOpen_boundary_numerator
    f hL d V c k n o W U hU hUW ha O hO P hSafe v t hb he

include ha in
/-- Local integrality of each independent bad quotient gives full boundary surjectivity. -/
theorem originalSource_coefficientwise_badQuotient_surjective
    (P : Ideal Tsource) [P.IsPrime]
    (h : ∀ t : Bsource, ∃ (O : U.toScheme.Opens)
      (hO : ∀ g : Equiv.Perm (Fin n), (τU g).hom ⁻¹ᵁ O = O)
      (J : Ideal Γ(U.toScheme, ⊤)),
      PrimeSpectrum.zeroLocus (J : Set Γ(U.toScheme, ⊤)) =
        U.toScheme.toSpecΓ '' (O : Set U.toScheme)ᶜ ∧
      (OriginalPrimeIntegralFiber.localizedMap
        ((Ideal.Quotient.mk J).comp σ₀) (P.comap κ)).IsIntegral ∧
      (∀ x : U.toScheme,
        SchemeScalarPrincipalNeighborhood.scalarMorphism σ₀ x =
          PrimeSpectrum.comap κ ⟨P, inferInstance⟩ → x ∈ O) ∧
      ∃ v : invariantCoordinates (restrictedAction τU O hO),
        ((jU) ∣_ O).appTop v.val = ((jU) ⁻¹ᵁ O).ι.appTop t.val ∧
        (pairOpenFirst O F H).appTop v.val = (pairOpenSecond O F H).appTop v.val) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  apply (originalSourceCompatible_surjective_iff_numerators
    f hL d V c k n o W U hU hUW P).mpr
  intro t
  obtain ⟨O, hO, J, hJ, hInt, hP, v, hb, he⟩ := h t
  exact originalSource_badQuotient_local_integral_numerator
    f hL d V c k n o W U hU hUW ha O hO J hJ P hInt hP v t hb he

end FLT.Mazur.HilbertChart.AffineRestriction
