/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeNormalizedTransfer
public import FLT.Mazur.SchemeNaturalUnitLocus

/-!
# Actual Hilbert source neighborhoods for unscaled transfer

A unit binomial degree in the original source stalk gives a canonical stable
affine neighborhood where normalization applies. All existing target-selection
inclusions survive this refinement. Only a stalk-unit hypothesis is used;
no coordinate-ring inverse or extra source lift is supplied as input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

variable (m' : ℕ) (a : Fin m')
  (U' : (normalizedFullRelationFrames f hL d V c k m' a).Opens)
  (hU' : ∀ σ : Equiv.Perm (Fin m'),
    (normalizedFullRelationAction f hL d V c k m' a σ).hom ⁻¹ᵁ U' = U')
  (h : ∀ ι : Fin m' ↪ Fin n,
    U ≤ subframeMap (fullRelationSchemeEquivalence f hL d V c k) o a ι ⁻¹ᵁ U')
  (hU'W : U' ≤ normalizedFullRelationFirst f hL d V c k m' a ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

include hU hUW h in
/-- Construct the actual stable affine source and an unscaled original boundary lift. -/
theorem exists_originalSubframe_unit_neighborhood
    (ha : IsAffineOpen U) (ha' : IsAffineOpen U')
    (x : normalizedFullRelationFrames f hL d V c k n o) (hx : x ∈ U)
    (hn : IsUnit (n.choose m' :
      (normalizedFullRelationFrames f hL d V c k n o).presheaf.stalk x)) :
    ∃ (Z : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hZ : ∀ σ, (τ σ).hom ⁻¹ᵁ Z = Z)
      (hZW : Z ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      IsAffineOpen Z ∧ x ∈ Z ∧ Z ≤ U ∧
      ∃ hZs : ∀ ι : Fin m' ↪ Fin n, Z ≤ subframeMap e o a ι ⁻¹ᵁ U',
      ∃ hNZ : IsUnit ((Fintype.card (Fin n)).choose (Fintype.card (Fin m')) :
          Γ(Z.toScheme, ⊤)),
      ∃ v : invariantCoordinates (restrictedAction
          (normalizedFullRelationAction f hL d V c k m' a) U' hU'),
        normalizedBoundaryChartMap f hL d V c k m' a U' hU' v =
          normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t ∧
        normalizedBoundaryChartMap f hL d V c k n o Z hZ
          (subframeNormalizedTransfer e o a Z hZ U' hU' hZs hNZ v) =
            normalizedOrbitBoundaryCoefficient f hL d V c k n o W Z hZ hZW t := by
  let Z := U ⊓ SchemeNaturalUnitLocus.locus N (n.choose m')
  have hZU : Z ≤ U := inf_le_left
  have hZ : ∀ σ, (τ σ).hom ⁻¹ᵁ Z = Z :=
    SchemeNaturalUnitLocus.stable_inter N (n.choose m') τ U hU
  have hZW := hZU.trans hUW
  have hZs (ι : Fin m' ↪ Fin n) := hZU.trans (h ι)
  have hNZ : IsUnit (n.choose m' : Γ(Z.toScheme, ⊤)) :=
    SchemeNaturalUnitLocus.isUnit_on N _ Z inf_le_right
  refine ⟨Z, hZ, hZW, SchemeNaturalUnitLocus.isAffineOpen_inter N _ U ha,
    SchemeNaturalUnitLocus.mem_inter N _ U x hx hn, hZU, hZs,
    (by simpa only [Fintype.card_fin] using hNZ), ?_⟩
  exact exists_originalSubframe_normalized_lift f hL d V c k n o W Z hZ hZW
    m' a U' hU' hZs hU'W t hNZ ha'

end FLT.Mazur.HilbertChart.AffineRestriction
