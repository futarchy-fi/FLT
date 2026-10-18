/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceCoefficientwiseSurjectivity
public import FLT.Mazur.HilbertSourceActionRelationGraph
public import FLT.Mazur.SchemeStableCoreInvariantSection
public import FLT.Mazur.SchemeStableCoreScalarNeighborhood

/-!
# Actual full Hilbert source lifts from arbitrary usable opens

The full relation equation on a raw open section constructs its permutation
overlap equations, a stable core, and the invariant section on that core.
Original scalar avoidance is preserved exactly. No stable usable open or
invariant local section is assumed as a separate input.
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

open SchemeFiniteOrbitOpenCore
variable (ha : IsAffineOpen U)

include ha in
/-- A raw open section solving the full pair equation yields an exact original numerator. -/
theorem originalSource_unstableOpen_boundary_numerator
    (O : U.toScheme.Opens) (P : Ideal Tsource) [P.IsPrime]
    (hP : PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈
      SchemeScalarPrincipalNeighborhood.scalarNeighborhoodLocus σ₀ O)
    (v : Γ(O.toScheme, ⊤)) (t : Bsource)
    (hb : ((jU) ∣_ O).appTop v = ((jU) ⁻¹ᵁ O).ι.appTop t.val)
    (he : (pairOpenFirst O F H).appTop v = (pairOpenSecond O F H).appTop v) :
    ∃ x₀ : Ω, κ x₀ ∉ P ∧ ∃ w : Sinv,
      normalizedBoundaryChartMap f hL d V c k n o U hU w =
        normalizedBoundaryChartMap f hL d V c k n o U hU (σ x₀) * t ∧
      w.val ∈ SchemeEffectiveEpiSections.compatibleFunctions F H := by
  let hf := finite_open_orbit τU O
  have hv := originalSource_pairOpen_action_equation f hL d V c k n o U hU O v he
  apply originalSource_pairOpen_boundary_numerator f hL d V c k n o W U hU hUW ha
    (invariantOpen τU O hf) (invariantOpen_stable τU O hf) P
    (by rwa [scalarNeighborhoodLocus_invariantOpen])
    (invariantCoreSection τU O hf v hv) t
  · exact invariantCoreSection_boundary τU O hf v hv jU t.val hb
  · exact invariantCoreSection_pair τU O hf v hv F H he

include ha in
/-- Coefficientwise raw usable opens suffice for surjectivity on the full localized source. -/
theorem originalSource_coefficientwise_unstableOpen_surjective
    (P : Ideal Tsource) [P.IsPrime]
    (h : ∀ t : Bsource, ∃ O : U.toScheme.Opens,
      PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈
        SchemeScalarPrincipalNeighborhood.scalarNeighborhoodLocus σ₀ O ∧
      ∃ v : Γ(O.toScheme, ⊤),
        ((jU) ∣_ O).appTop v = ((jU) ⁻¹ᵁ O).ι.appTop t.val ∧
        (pairOpenFirst O F H).appTop v = (pairOpenSecond O F H).appTop v) :
    let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
    let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
    Function.Surjective
      (originalSourceLocalizedCompatibleBoundaryMap f hL d V c k n o W U hU hUW P) := by
  let _ := normalizedOriginalChartAlgebra f hL d V c k n o W U hU hUW
  let _ := normalizedOriginalBoundaryAlgebra f hL d V c k n o W U hU hUW
  apply (originalSourceCompatible_surjective_iff_numerators
    f hL d V c k n o W U hU hUW P).mpr
  intro t
  obtain ⟨O, hSafe, v, hb, he⟩ := h t
  exact originalSource_unstableOpen_boundary_numerator
    f hL d V c k n o W U hU hUW ha O P hSafe v t hb he

include ha in
/-- The original bad quotient can be checked on the nonstable open before refinement. -/
theorem originalSource_unstableOpen_badQuotient_numerator
    (O : U.toScheme.Opens) (J : Ideal Γ(U.toScheme, ⊤))
    (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(U.toScheme, ⊤)) =
      U.toScheme.toSpecΓ '' (O : Set U.toScheme)ᶜ)
    (P : Ideal Tsource) [P.IsPrime]
    (hInt : (OriginalPrimeIntegralFiber.localizedMap
      ((Ideal.Quotient.mk J).comp σ₀) (P.comap κ)).IsIntegral)
    (hP : ∀ x : U.toScheme,
      SchemeScalarPrincipalNeighborhood.scalarMorphism σ₀ x =
        PrimeSpectrum.comap κ ⟨P, inferInstance⟩ → x ∈ O)
    (v : Γ(O.toScheme, ⊤)) (t : Bsource)
    (hb : ((jU) ∣_ O).appTop v = ((jU) ⁻¹ᵁ O).ι.appTop t.val)
    (he : (pairOpenFirst O F H).appTop v = (pairOpenSecond O F H).appTop v) :
    ∃ x₀ : Ω, κ x₀ ∉ P ∧ ∃ w : Sinv,
      normalizedBoundaryChartMap f hL d V c k n o U hU w =
        normalizedBoundaryChartMap f hL d V c k n o U hU (σ x₀) * t ∧
      w.val ∈ SchemeEffectiveEpiSections.compatibleFunctions F H := by
  let _ : IsAffine U.toScheme := ha
  apply originalSource_unstableOpen_boundary_numerator
    f hL d V c k n o W U hU hUW ha O P _ v t hb he
  exact SchemeScalarPrincipalNeighborhood.mem_scalarNeighborhoodLocus_of_badQuotient_local_integral
    σ₀ J O hJ (PrimeSpectrum.comap κ ⟨P, inferInstance⟩) hInt hP

end FLT.Mazur.HilbertChart.AffineRestriction
