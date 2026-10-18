/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeOriginalScalars

public import FLT.Mazur.SchemeOriginalScalarCompactRelationLifts
public import FLT.Mazur.SchemeRelationDoubleRestriction

/-!
# Constructing original Hilbert source lifts on full relations

Original invariant scalars equalize the entire two-endpoint source relation.
For a quasicompact source relation, an open-compatible boundary lift and an
original safe prime construct a full-compatible source numerator with exact
scaled boundary. No complete-open hypothesis or residual-emptiness assertion
is used. Existence of the local boundary lift and a safe prime remains open.
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

omit [Etale V.hom] in
/-- Original Hilbert scalars equalize the full restricted source relation. -/
theorem normalizedOriginalScalarMap_full_source_relation (x : Ω) :
    (F).appTop (σ x).val = (H).appTop (σ x).val := by
  simp only [normalizedOriginalScalarMap_val]
  apply open_scalar_test E (pullOpen_preimage_eq eo W) (orbitFunctions eo W x).val
    (OrbitBoundaryAtlas.FiniteAtlas.original_scalar_equalized f hL d V c k W x)
    (F ≫ (normalizedFullRelationFirst f hL d V c k n o).resLE E U hUW)
    (H ≫ (normalizedFullRelationFirst f hL d V c k n o).resLE E U hUW)
    (SchemeRelationRestriction.arrow p q kS)
  · simpa only [Category.assoc, Scheme.Hom.resLE_comp_ι] using
      SchemeRelationRestriction.arrow_fst p q kS
  · simpa only [Category.assoc, Scheme.Hom.resLE_comp_ι] using
      SchemeRelationRestriction.arrow_snd p q kS

variable (ha : IsAffineOpen U) [CompactSpace
  (SchemeRelationRestriction.doubleDomain
    (Over.Hom.left (AffineRestriction.fst f hL d V c k))
    (Over.Hom.left (AffineRestriction.snd f hL d V c k))
    (U.ι ≫ normalizedFullRelationFirst f hL d V c k n o))]
  (O : U.toScheme.Opens)
  (hO : ∀ g : Equiv.Perm (Fin n),
    (restrictedAction (normalizedFullRelationAction f hL d V c k n o) U hU g).hom ⁻¹ᵁ O = O)

include ha in
/-- Local open equations construct the full original source lift at the original boundary prime. -/
theorem originalSource_pairOpen_full_relation_lift
    (P : Ideal Tsource) [P.IsPrime]
    (hP : PrimeSpectrum.comap κ ⟨P, inferInstance⟩ ∈
      SchemeScalarPrincipalNeighborhood.scalarNeighborhoodLocus σ₀ O)
    (v : invariantCoordinates (restrictedAction τU O hO))
    (t : Γ((j ⁻¹ᵁ U).toScheme, ⊤))
    (hb : ((jU) ∣_ O).appTop v.val = ((jU) ⁻¹ᵁ O).ι.appTop t)
    (he : (pairOpenFirst O F H).appTop v.val = (pairOpenSecond O F H).appTop v.val) :
    ∃ x₀ : Ω, κ x₀ ∉ P ∧ ∃ w : Sinv,
      (jU).appTop w.val = (jU).appTop (σ x₀).val * t ∧
        w.val ∈ SchemeEffectiveEpiSections.compatibleFunctions F H := by
  let _ : IsAffine U.toScheme := ha
  let _ := isAffine_of_isAffineHom jU
  exact originalScalar_compact_relation_lift τU σ O hO jU F H
    (normalizedOriginalScalarMap_full_source_relation f hL d V c k n o W U hU hUW)
    (PrimeSpectrum.comap κ ⟨P, inferInstance⟩) hP v t hb he

end FLT.Mazur.HilbertChart.AffineRestriction
