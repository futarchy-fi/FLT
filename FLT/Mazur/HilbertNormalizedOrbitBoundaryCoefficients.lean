/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryQuotientSections
public import FLT.Mazur.HilbertNormalizedBoundaryChartLifts
public import FLT.Mazur.HilbertNormalizedAffineRefinement
public import FLT.Mazur.EquivalenceRelationBoundaryOpenCoefficients
public import FLT.Mazur.RelativeRelationOpenFunctionMap
public import FLT.Mazur.RelativeRelationClosedSections

/-!
# Moving chart coefficients for every original orbit-domain boundary section

The input is an arbitrary section of the original boundary invariant sheaf on
an arbitrary orbit open. Its exact function, including nilpotents, supplies an
invariant coefficient on every moving chart over that domain. Affine charts
lift it. Exhaustive comparison with the entire original relation is separate.
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

include hUW in
/-- The entire chart boundary lies over the actual boundary orbit domain. -/
theorem normalizedOrbitBoundary_domain_le : (j) ⁻¹ᵁ U ≤ (b) ⁻¹ᵁ Uc := by
  have hv : Uc = (i) ⁻¹ᵁ (pullOpen eo W).val :=
    invariantMap_sourceOpen_eq eo ec i z (originalClosedArrow_left_fst f hL d V c k)
      (originalClosedArrow_left_snd f hL d V c k) W
  rw [hv]
  exact InvariantBoundary.boundary_chart_le (Fin n) o (pullOpen eo W).val i U hUW

variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Every original boundary sheaf section defines its exact moving-chart coefficient. -/
def normalizedOrbitBoundaryCoefficient :
    invariantCoordinates (boundaryOpenAction ρ τ j hj U hU) :=
  InvariantBoundary.domainInvariantCoefficient e (Fin n) o i z r s hr hs Uc
    (pullOpen_preimage_eq ec Wc) U hU
    (normalizedOrbitBoundary_domain_le f hL d V c k n o W U hUW)
    (orbitFunctions ec Wc t).val (by
      have h := (orbitFunctions ec Wc t).property
      change ((r).resLE Uc _ le_rfl).appTop (orbitFunctions ec Wc t).val =
        ((s).resLE Uc _ (pullOpen_preimage_eq ec Wc).le).appTop
          (orbitFunctions ec Wc t).val at h
      simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using h)

/-- The coefficient is the actual original section, not a chosen global extension. -/
theorem normalizedOrbitBoundaryCoefficient_val :
    (normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t).val =
      ((b).resLE Uc (j ⁻¹ᵁ U)
        (normalizedOrbitBoundary_domain_le f hL d V c k n o W U hUW)).appTop
        (orbitFunctions ec Wc t).val := rfl

/-- Every original orbit-domain section lifts on each affine moving source chart above it. -/
theorem normalizedOrbitBoundaryCoefficient_lift (ha : IsAffineOpen U) :
    ∃ a, normalizedBoundaryChartMap f hL d V c k n o U hU a =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t :=
  boundaryOpen_invariantMap_surjective ρ τ j hj U hU
    (fun _ _ a σ h ↦ EquivalenceRelationNormalizedFrames.action_free e (Fin n) o a σ h) ha _

/-- These coefficients have finite identities on the exact closed affine chart. -/
theorem normalizedOrbitBoundaryCoefficient_certificate (ha : IsAffineOpen U) :
    ∃ a : sectionLiftIdeal (normalizedBoundaryChartMap f hL d V c k n o U hU)
        (normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t) →₀
          Γ((j ⁻¹ᵁ U).toScheme, ⊤),
      a.sum (fun v coeff ↦ coeff *
        (normalizedBoundaryChartMap f hL d V c k n o U hU v.val).val) = 1 :=
  boundaryOpen_certificate ρ τ j hj U hU
    (fun _ _ a σ h ↦ EquivalenceRelationNormalizedFrames.action_free e (Fin n) o a σ h) ha _

end FLT.Mazur.HilbertChart.AffineRestriction
