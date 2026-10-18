/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeExchangeObstruction

/-!
# Exact original embedding lifts from the target exchange obstruction

Vanishing of the concrete target correction class constructs both invariant
lifts and every unscaled embedding equation. Conversely, any compatible pair
kills that class. No binomial degree is inverted, so this reduction also holds
for strict prime-power sizes in their defining residue characteristic.
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

/-- A zero target correction class gives exact original lifts without degree inversion. -/
theorem originalSubframeExchangeClass_compatible_lifts
    (hb₀ : b₀ ∉ Set.range ι) (v : Tinv) (hv : β v = tT) (hz : cls v = 0) :
    ∃ (u : Sinv) (w : Tinv), α u = tS ∧ β w = tT ∧
      ∀ κ : Fin m' ↪ Fin n,
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι κ).ι ≫
          mixedChartFirst o a U U').appTop u.val =
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι κ).ι ≫
          mixedChartSecond o a U U').appTop w.val := by
  obtain ⟨zeta, hb, hd⟩ := (originalSubframeExchangeClass_zero_iff
    f hL d V c k n o U m' a U' hU' h ι b₀ v).mp hz
  let w := v - zeta
  have hw : β w = tT := by
    change β (v - zeta) = _
    rw [map_sub, hv, hb, sub_zero]
  have hex : δ w = 0 := by
    change δ (v - zeta) = 0
    rw [map_sub, hd, sub_self]
  have hi := (subframeExchangeMap_zero_iff_invariant e o a U U' hU' h
    hU ι b₀ hb₀ w).mp hex
  have ha := (subframePullback_invariant_iff e o a U hU U' h ι w.val).mp hi
  obtain ⟨u, hu, hbranches⟩ := exists_invariant_subframe_branch_lift
    e o a U U' hU h ι w.val ha
  refine ⟨u, w, ?_, hw, hbranches⟩
  apply Subtype.ext
  change ((j) ∣_ U).appTop u.val = (tS).val
  rw [hu]
  exact normalizedOrbitBoundaryLift_subframeRefinement f hL d V c k n o W U hU hUW
    m' a ι U' hU' (h ι) hU'W t w hw

/-- Any actual compatible original pair kills the same target exchange class. -/
theorem originalSubframeExchangeClass_zero_of_compatible
    (hb₀ : b₀ ∉ Set.range ι) (v : Tinv) (hv : β v = tT)
    (u : Sinv) (w : Tinv) (hw : β w = tT)
    (he : ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι ι).ι ≫
        mixedChartFirst o a U U').appTop u.val =
      ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι ι).ι ≫
        mixedChartSecond o a U U').appTop w.val) : cls v = 0 := by
  have hi := (mixedSubframeBranch_equation_iff e o a U U' ι (h ι) u.val w.val).mp he
  have hex := (subframeExchangeMap_zero_iff_invariant e o a U U' hU' h
    hU ι b₀ hb₀ w).mpr ⟨u, hi⟩
  rw [originalSubframeExchangeClass_independent f hL d V c k n o U
    m' a U' hU' h ι b₀ v w (hv.trans hw.symm)]
  change BoundaryExchangeObstruction.liftClass
    (β).toAddMonoidHom.toIntLinearMap (δ).toIntLinearMap w = 0
  exact (BoundaryExchangeObstruction.liftClass_zero_iff_lift
    (β).toAddMonoidHom.toIntLinearMap (δ).toIntLinearMap w).mpr ⟨w, rfl, hex⟩

/-- The precise target obstruction to all original unscaled embedding equations. -/
theorem originalSubframeExchangeClass_zero_iff_compatible
    (hb₀ : b₀ ∉ Set.range ι) (v : Tinv) (hv : β v = tT) :
    cls v = 0 ↔ ∃ (u : Sinv) (w : Tinv), α u = tS ∧ β w = tT ∧
      ∀ κ : Fin m' ↪ Fin n,
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι κ).ι ≫
          mixedChartFirst o a U U').appTop u.val =
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U U').ι κ).ι ≫
          mixedChartSecond o a U U').appTop w.val := by
  constructor
  · exact originalSubframeExchangeClass_compatible_lifts f hL d V c k n o W U hU hUW
      m' a U' hU' h hU'W t ι b₀ hb₀ v hv
  · rintro ⟨u, w, _, hw, he⟩
    exact originalSubframeExchangeClass_zero_of_compatible f hL d V c k n o W U hU
      m' a U' hU' h hU'W t ι b₀ hb₀ v hv u w hw (he ι)

end FLT.Mazur.HilbertChart.AffineRestriction
