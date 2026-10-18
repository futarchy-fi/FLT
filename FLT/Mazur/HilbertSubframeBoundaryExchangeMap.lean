/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedBoundarySurjectivity
public import FLT.Mazur.HilbertSubframeExchangeLifts

/-!
# A canonical exchange obstruction on actual original boundary coefficients

Surjectivity of the affine target boundary map constructs an additive boundary
obstruction independent of lifts. For original orbit coefficients, its vanishing
is exactly existence of a compatible invariant pair on every embedding branch.
The zero test is independent of the selected embedding and omitted label.
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

open EquivalenceRelationNormalizedFrames.MixedFrames
local notation "Sinv" => invariantCoordinates (restrictedAction τ U hU)
local notation "α" => normalizedBoundaryChartMap f hL d V c k n o U hU
local notation "tS" => normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t
local notation "tT" => normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t
local notation "cls" => originalSubframeExchangeClass
  f hL d V c k n o U m' a U' hU' h ι b₀

local notation "ρT" => normalizedOriginalBoundaryAction f hL d V c k m' a
local notation "τT" => normalizedFullRelationAction f hL d V c k m' a
local notation "jT" => normalizedOriginalBoundaryInclusion f hL d V c k m' a
local notation "hjT" => normalizedOriginalBoundaryAction_inclusion f hL d V c k m' a
local notation "Btarget" => invariantCoordinates (boundaryOpenAction ρT τT jT hjT U' hU')

/-- The actual affine target gives a canonical exchange operator on its boundary ring. -/
def originalSubframeBoundaryExchangeMap (ha' : IsAffineOpen U') :
    Btarget →ₗ[ℤ] (Γ(U.toScheme, ⊤) ⧸
      originalSubframeExchangeCorrectionImage f hL d V c k n o U m' a U' hU' h ι b₀) :=
  BoundaryExchangeObstruction.boundaryMap
    (β).toAddMonoidHom.toIntLinearMap (δ).toIntLinearMap
    (normalizedBoundaryChartMap_surjective f hL d V c k m' a U' hU' ha')

/-- Every independent target lift computes the same canonical boundary operator. -/
theorem originalSubframeBoundaryExchangeMap_apply (ha' : IsAffineOpen U') (v : Tinv) :
    originalSubframeBoundaryExchangeMap f hL d V c k n o U m' a U' hU' h ι b₀ ha'
      (β v) = cls v :=
  BoundaryExchangeObstruction.boundaryMap_apply
    (β).toAddMonoidHom.toIntLinearMap (δ).toIntLinearMap _ v

/-- The original boundary coefficient has zero obstruction exactly when embedding lifts exist. -/
theorem originalSubframeBoundaryExchangeMap_zero_iff
    (ha' : IsAffineOpen U') (hb₀ : b₀ ∉ Set.range ι) :
    originalSubframeBoundaryExchangeMap f hL d V c k n o U m' a U' hU' h ι b₀ ha'
      tT = 0 ↔ ∃ (u : Sinv) (w : Tinv), α u = tS ∧ β w = tT ∧
      ∀ κ : Fin m' ↪ Fin n,
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι κ).ι ≫
          mixedChartFirst o a U U').appTop u.val =
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι κ).ι ≫
          mixedChartSecond o a U U').appTop w.val := by
  obtain ⟨v, hv⟩ := normalizedOrbitBoundaryCoefficient_lift
    f hL d V c k m' a W U' hU' hU'W t ha'
  have he := originalSubframeBoundaryExchangeMap_apply
    f hL d V c k n o U m' a U' hU' h ι b₀ ha' v
  rw [hv] at he
  rw [he]
  exact originalSubframeExchangeClass_zero_iff_compatible
    f hL d V c k n o W U hU hUW m' a U' hU' h hU'W t ι b₀ hb₀ v hv

include hU hUW in
/-- The zero obstruction is independent of both choices in the single exchange test. -/
theorem originalSubframeBoundaryExchangeMap_zero_choice
    (ha' : IsAffineOpen U') (hb₀ : b₀ ∉ Set.range ι)
    (κ : Fin m' ↪ Fin n) (c₀ : Fin n) (hc₀ : c₀ ∉ Set.range κ) :
    originalSubframeBoundaryExchangeMap f hL d V c k n o U m' a U' hU' h ι b₀ ha'
      tT = 0 ↔
    originalSubframeBoundaryExchangeMap f hL d V c k n o U m' a U' hU' h κ c₀ ha'
      tT = 0 := by
  rw [originalSubframeBoundaryExchangeMap_zero_iff
    f hL d V c k n o W U hU hUW m' a U' hU' h hU'W t ι b₀ ha' hb₀,
    originalSubframeBoundaryExchangeMap_zero_iff
      f hL d V c k n o W U hU hUW m' a U' hU' h hU'W t κ c₀ ha' hc₀]

end FLT.Mazur.HilbertChart.AffineRestriction
