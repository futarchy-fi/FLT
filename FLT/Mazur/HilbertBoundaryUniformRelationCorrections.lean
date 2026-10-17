/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedOrbitBoundaryCoefficients
public import FLT.Mazur.EquivalenceRelationUniformVanishingOpen
public import FLT.Mazur.VariableHilbertNoetherianSource

/-!
# A single original relation neighborhood for every boundary section

The open is chosen before the boundary section. Every original boundary
section has a moving-invariant lift equalizing the full original endpoints
on that same open, which contains all complete first-endpoint fibers.
This constructs uniform relation corrections, not original source scalars.
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

local notation "F" => SourceRestriction.fst U.ι U.ι
local notation "G" => SourceRestriction.snd U.ι U.ι
local notation "T" => SourceRestriction.relation U.ι U.ι

/-- One actual relation open works for every original boundary section simultaneously. -/
theorem normalizedOrbitBoundary_uniform_relation_neighborhood (ha : IsAffineOpen U) :
    ∃ O : (T).Opens,
      ((F) ≫ U.ι) ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o ⊆ O ∧
      ∀ t : (invariantSheaf ec).obj.obj (op Wc),
        ∃ a, normalizedBoundaryChartMap f hL d V c k n o U hU a =
            normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t ∧
          (O.ι ≫ (F)).appTop a.val = (O.ι ≫ (G)).appTop a.val := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  refine ⟨completeUniformRelationVanishingOpen e (Fin n) o U hU,
    completeUniformRelationVanishingOpen_contains e (Fin n) o U hU, ?_⟩
  intro t
  obtain ⟨a, ha⟩ := normalizedOrbitBoundaryCoefficient_lift f hL d V c k n o W U hU hUW t ha
  exact ⟨a, ha, completeUniformRelationVanishingOpen_equalizes e (Fin n) o U hU a⟩

/-- One fixed original relation open supports exact kernel corrections for every boundary lift. -/
theorem normalizedOrbitBoundary_uniform_kernel_corrections (ha : IsAffineOpen U) :
    ∃ O : (T).Opens,
      ((F) ≫ U.ι) ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o ⊆ O ∧
      ∀ (t : (invariantSheaf ec).obj.obj (op Wc))
        (u : invariantCoordinates (restrictedAction τ U hU)),
        normalizedBoundaryChartMap f hL d V c k n o U hU u =
          normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t →
        ∃ v, v ∈ RingHom.ker (normalizedBoundaryChartMap f hL d V c k n o U hU) ∧
          (O.ι ≫ (F)).appTop v.val - (O.ι ≫ (G)).appTop v.val =
            (O.ι ≫ (F)).appTop u.val - (O.ι ≫ (G)).appTop u.val := by
  obtain ⟨O, hO, hlift⟩ :=
    normalizedOrbitBoundary_uniform_relation_neighborhood f hL d V c k n o W U hU hUW ha
  refine ⟨O, hO, ?_⟩
  intro t u hu
  obtain ⟨a, ha, he⟩ := hlift t
  refine ⟨u - a, ?_, ?_⟩
  · change normalizedBoundaryChartMap f hL d V c k n o U hU (u - a) = 0
    rw [map_sub, hu, ha, sub_self]
  · change (O.ι ≫ (F)).appTop (u.val - a.val) -
      (O.ι ≫ (G)).appTop (u.val - a.val) = _
    rw [map_sub, map_sub, he]
    ring

end FLT.Mazur.HilbertChart.AffineRestriction
