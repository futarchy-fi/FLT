/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeExchangeMap
public import FLT.Mazur.BoundaryExchangeObstruction
public import FLT.Mazur.HilbertSubframeBoundaryLifts

/-!
# The exchange obstruction of an original Hilbert boundary coefficient

The actual exchange of an exact target lift vanishes on the entire original
source boundary. Quotienting by exchanges of target boundary-kernel elements
makes the obstruction independent of the chosen target lift. This quotient
uses only integer scalars and does not assert local vanishing.
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

variable (ι : Fin m' ↪ Fin n) (b₀ : Fin n)
local notation "Tinv" => invariantCoordinates (restrictedAction
  (normalizedFullRelationAction f hL d V c k m' a) U' hU')
local notation "β" => normalizedBoundaryChartMap f hL d V c k m' a U' hU'
local notation "δ" => subframeExchangeMap e o a U U' hU' h ι b₀

include hU hUW in
/-- The actual exchange of an exact lift is zero on the unreduced source boundary. -/
theorem normalizedOrbitBoundary_subframeExchange_zero (v : Tinv)
    (hv : β v = normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t) :
    ((j) ∣_ U).appTop (δ v) = 0 := by
  change ((j) ∣_ U).appTop
    ((subframeRefinementMap e o a _ U U' _).appTop v.val -
      (subframeRefinementMap e o a ι U U' (h ι)).appTop v.val) = 0
  rw [map_sub,
    normalizedOrbitBoundaryLift_subframeRefinement f hL d V c k n o W U hU hUW
      m' a _ U' hU' (h _) hU'W t v hv,
    normalizedOrbitBoundaryLift_subframeRefinement f hL d V c k n o W U hU hUW
      m' a ι U' hU' (h ι) hU'W t v hv, sub_self]

/-- The correction space consists of exchanges of actual target boundary-kernel elements. -/
def originalSubframeExchangeCorrectionImage : Submodule ℤ Γ(U.toScheme, ⊤) :=
  BoundaryExchangeObstruction.correctionImage (β).toAddMonoidHom.toIntLinearMap (δ).toIntLinearMap

/-- The original exchange class of a chosen target lift. -/
def originalSubframeExchangeClass :
    Tinv →ₗ[ℤ] (Γ(U.toScheme, ⊤) ⧸
      originalSubframeExchangeCorrectionImage f hL d V c k n o U m' a U' hU' h ι b₀) :=
  BoundaryExchangeObstruction.liftClass (β).toAddMonoidHom.toIntLinearMap (δ).toIntLinearMap

/-- Independent exact lifts give the same actual target correction obstruction. -/
theorem originalSubframeExchangeClass_independent (v w : Tinv) (hv : β v = β w) :
    originalSubframeExchangeClass f hL d V c k n o U m' a U' hU' h ι b₀ v =
      originalSubframeExchangeClass f hL d V c k n o U m' a U' hU' h ι b₀ w :=
  BoundaryExchangeObstruction.liftClass_eq_of_boundary_eq
    (β).toAddMonoidHom.toIntLinearMap (δ).toIntLinearMap v w hv

/-- Vanishing gives a genuine target boundary-zero correction with the required exchange. -/
theorem originalSubframeExchangeClass_zero_iff (v : Tinv) :
    originalSubframeExchangeClass f hL d V c k n o U m' a U' hU' h ι b₀ v = 0 ↔
      ∃ zeta : Tinv, β zeta = 0 ∧ δ zeta = δ v :=
  BoundaryExchangeObstruction.liftClass_zero_iff
    (β).toAddMonoidHom.toIntLinearMap (δ).toIntLinearMap v

end FLT.Mazur.HilbertChart.AffineRestriction
