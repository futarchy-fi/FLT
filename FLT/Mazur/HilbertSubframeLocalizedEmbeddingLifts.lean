/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeOriginalLocalization
public import FLT.Mazur.EquivalenceRelationBoundarySubframeKernel

/-!
# Denominator-cleared compatible lifts on the original embedding branches

A vanishing original-scalar localized class gives a denominator and actual
invariant source and target lifts. Both have the correctly scaled original
boundary coefficients and satisfy every embedding branch equation. The
statement retains the exact localization hypothesis; it does not prove it.
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

variable (m' : ℕ) (a : Fin m')
  (U' : (normalizedFullRelationFrames f hL d V c k m' a).Opens)
  (hU' : ∀ σ : Equiv.Perm (Fin m'),
    (normalizedFullRelationAction f hL d V c k m' a σ).hom ⁻¹ᵁ U' = U')
  (hU'W : U' ≤ normalizedFullRelationFirst f hL d V c k m' a ⁻¹ᵁ
    (pullOpen (equivalence f hL d V c k) W).val)
local notation "Tinv" => invariantCoordinates (restrictedAction
  (normalizedFullRelationAction f hL d V c k m' a) U' hU')

variable (h : ∀ ι : Fin m' ↪ Fin n,
    U ≤ subframeMap (fullRelationSchemeEquivalence f hL d V c k) o a ι ⁻¹ᵁ U')
  (ι : Fin m' ↪ Fin n) (b₀ : Fin n)
local notation "β" => normalizedOriginalBoundaryHom f hL d V c k m' a W U' hU' hU'W
local notation "δ" => originalSubframeExchangeLinearMap
  f hL d V c k n o W U hU hUW m' a U' hU' hU'W h ι b₀
local notation "Btarget" => invariantCoordinates (boundaryOpenAction
  (normalizedOriginalBoundaryAction f hL d V c k m' a)
  (normalizedFullRelationAction f hL d V c k m' a)
  (normalizedOriginalBoundaryInclusion f hL d V c k m' a)
  (normalizedOriginalBoundaryAction_inclusion f hL d V c k m' a) U' hU')

local notation "K" => originalScalarExchangeCorrections
  f hL d V c k n o W U hU hUW m' a U' hU' hU'W h ι b₀
local notation "σS" => normalizedOriginalScalarMap f hL d V c k n o W U hU hUW
local notation "σT" => normalizedOriginalScalarMap f hL d V c k m' a W U' hU' hU'W
local notation "β₀" => normalizedBoundaryChartMap f hL d V c k m' a U' hU'
local notation "δ₀" => subframeExchangeMap e o a U U' hU' h ι b₀
variable (M : Submonoid ((invariantSheaf (equivalence f hL d V c k)).obj.obj (op W)))

variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
local notation "α" => normalizedBoundaryChartMap f hL d V c k n o U hU
local notation "tS" => normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t
local notation "tT" => normalizedOrbitBoundaryCoefficient f hL d V c k m' a W U' hU' hU'W t
open EquivalenceRelationNormalizedFrames.MixedFrames

attribute [local irreducible] normalizedOriginalScalarMap originalLocalizedExchangeClass
  originalScalarExchangeCorrections originalSubframeExchangeLinearMap

/-- An independently chosen scaled target lift has the correct selected source boundary. -/
theorem normalizedScaledBoundaryLift_subframe (x : Ω) (v w : Tinv)
    (hv : β₀ v = tT) (hw : β₀ w = β₀ (σT x) * β₀ v) :
    ((j) ∣_ U).appTop ((subframeRefinementMap e o a ι U U' (h ι)).appTop w.val) =
      (α (σS x)).val * (tS).val := by
  have hd : β₀ (w - σT x * v) = 0 := by
    rw [map_sub, map_mul, hw, sub_self]
  have hk := InvariantBoundary.subframeBoundaryRefinement_kernel
    e o a i z r s hr hs U U' ι (h ι) (w - σT x * v).val
    (congrArg Subtype.val hd)
  change ((j) ∣_ U).appTop
    ((subframeRefinementMap e o a ι U U' (h ι)).appTop
      (w.val - (σT x * v).val)) = 0 at hk
  rw [map_sub, map_sub] at hk
  rw [sub_eq_zero.mp hk, Subring.coe_mul, map_mul,
    normalizedOriginalScalarMap_subframe f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W ι (h ι), map_mul,
    normalizedOrbitBoundaryLift_subframeRefinement f hL d V c k n o W U hU hUW
      m' a ι U' hU' (h ι) hU'W t v hv]
  rfl

/-- Local vanishing constructs compatible scaled lifts on every actual embedding branch. -/
theorem originalLocalizedExchangeClass_embedding_lifts
    (hb₀ : b₀ ∉ Set.range ι) (v : Tinv) (hv : β₀ v = tT)
    (hz : originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ M v = 0) :
    ∃ x : M, ∃ (u : Sinv) (w : Tinv),
      α u = α (σS x.val) * tS ∧ β₀ w = β₀ (σT x.val) * tT ∧
      ∀ κ : Fin m' ↪ Fin n,
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι κ).ι ≫
          mixedChartFirst o a U U').appTop u.val =
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι κ).ι ≫
          mixedChartSecond o a U U').appTop w.val := by
  obtain ⟨x, w, hw, hex⟩ := (originalLocalizedExchangeClass_zero_iff_lift
    f hL d V c k n o W U hU hUW m' a U' hU' hU'W h ι b₀ M v).mp hz
  have hi := (subframeExchangeMap_zero_iff_invariant e o a U U' hU' h
    hU ι b₀ hb₀ w).mp hex
  have ha := (subframePullback_invariant_iff e o a U hU U' h ι w.val).mp hi
  obtain ⟨u, hu, hbranches⟩ := exists_invariant_subframe_branch_lift
    e o a U U' hU h ι w.val ha
  refine ⟨x, u, w, ?_, by simpa only [hv] using hw, hbranches⟩
  apply Subtype.ext
  change ((j) ∣_ U).appTop u.val = _
  rw [hu]
  exact normalizedScaledBoundaryLift_subframe f hL d V c k n o W U hU hUW
    m' a U' hU' hU'W h ι t x.val v w hv hw

/-- Actual scaled embedding lifts characterize local exchange vanishing exactly. -/
theorem originalLocalizedExchangeClass_zero_iff_embedding
    (hb₀ : b₀ ∉ Set.range ι) (v : Tinv) (hv : β₀ v = tT) :
    originalLocalizedExchangeClass f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ M v = 0 ↔
    ∃ x : M, ∃ (u : Sinv) (w : Tinv),
      α u = α (σS x.val) * tS ∧ β₀ w = β₀ (σT x.val) * tT ∧
      ∀ κ : Fin m' ↪ Fin n,
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι κ).ι ≫
          mixedChartFirst o a U U').appTop u.val =
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι κ).ι ≫
          mixedChartSecond o a U U').appTop w.val := by
  constructor
  · exact originalLocalizedExchangeClass_embedding_lifts f hL d V c k n o W U hU hUW
      m' a U' hU' hU'W h ι b₀ M t hb₀ v hv
  · rintro ⟨x, u, w, _, hw, he⟩
    rw [originalLocalizedExchangeClass_zero_iff_lift]
    refine ⟨x, w, by simpa only [hv] using hw, ?_⟩
    apply (subframeExchangeMap_zero_iff_invariant e o a U U' hU' h hU ι b₀ hb₀ w).mpr
    exact ⟨u, (mixedSubframeBranch_equation_iff e o a U U' ι (h ι) u.val w.val).mp (he ι)⟩

end FLT.Mazur.HilbertChart.AffineRestriction
