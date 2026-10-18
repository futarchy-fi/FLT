/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSourceCompactRelation
public import FLT.Mazur.OriginalScalarFiniteRelationNumerators

/-!
# Simultaneous original source numerators from independent usable opens

Each boundary coefficient may have its own compatible lift on its own usable
open. Finitely many such choices yield full-relation source numerators with
one common scalar outside the unchanged original boundary prime.
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

variable (ha : IsAffineOpen U)
attribute [local irreducible] normalizedFullRelationFrames normalizedFullRelationFirst

include ha in
/-- Independent open solutions for finitely many coefficients have a common original denominator. -/
theorem originalSource_finite_pairOpen_lifts {I : Type} [Finite I]
    (P : Ideal Tsource) [P.IsPrime] (t : I → Γ((j ⁻¹ᵁ U).toScheme, ⊤))
    (h : ∀ a, ∃ (O : U.toScheme.Opens)
      (hO : ∀ g : Equiv.Perm (Fin n), (τU g).hom ⁻¹ᵁ O = O),
      PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈
        SchemeScalarPrincipalNeighborhood.scalarNeighborhoodLocus σ₀ O ∧
      ∃ v : invariantCoordinates (restrictedAction τU O hO),
        ((jU) ∣_ O).appTop v.val = ((jU) ⁻¹ᵁ O).ι.appTop (t a) ∧
        (pairOpenFirst O F H).appTop v.val = (pairOpenSecond O F H).appTop v.val) :
    ∃ x₀ : Ω, κ x₀ ∉ P ∧ ∃ w : I → Sinv,
      ∀ a, (jU).appTop (w a).val = (jU).appTop (σ x₀).val * t a ∧
        (w a).val ∈ SchemeEffectiveEpiSections.compatibleFunctions F H := by
  let β : Sinv →+* Γ((j ⁻¹ᵁ U).toScheme, ⊤) :=
    (jU).appTop.hom.comp (Subring.subtype _)
  let F₀ : Sinv →+* Γ(D, ⊤) := (F).appTop.hom.comp (Subring.subtype _)
  let H₀ : Sinv →+* Γ(D, ⊤) := (H).appTop.hom.comp (Subring.subtype _)
  have hσ : ∀ x₀, F₀ (σ x₀) = H₀ (σ x₀) :=
    normalizedOriginalScalarMap_full_source_relation f hL d V c k n o W U hU hUW
  apply OriginalScalarFiniteRelationNumerators.exists_common_numerator
    σ β F₀ H₀ hσ (P.comap κ) t
  intro a
  obtain ⟨O, hO, hP, v, hb, he⟩ := h a
  exact originalSource_pairOpen_lift f hL d V c k n o W U hU hUW
    ha O hO P hP v (t a) hb he

end FLT.Mazur.HilbertChart.AffineRestriction
