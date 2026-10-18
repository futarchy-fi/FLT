/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertSubframeConstructedUnitLift
public import FLT.Mazur.EquivalenceRelationSubframeEqualSize

/-!
# Constructed compatible lifts for equal-size original frame charts

At every original normalized source point construct an independent target
chart and an affine source refinement. The two unscaled boundary lifts agree
on every actual equal-size embedding branch. This includes prime-power sizes
in their defining residue characteristic; no strict-size claim is made.
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

variable (a : Fin n)
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))
attribute [local irreducible] normalizedBoundaryChartMap normalizedOrbitBoundaryCoefficient
open EquivalenceRelationNormalizedFrames.MixedFrames

include hU in
/-- Equal-size source and target charts have exact lifts solving all embedding equations. -/
theorem exists_originalSubframe_equal_size_compatible_lifts
    (x : normalizedFullRelationFrames f hL d V c k n o) (hxU : x ∈ U)
    (hxW : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val) :
    ∃ (T : (normalizedFullRelationFrames f hL d V c k n a).Opens)
      (hT : ∀ σ, (normalizedFullRelationAction f hL d V c k n a σ).hom ⁻¹ᵁ T = T)
      (hTW : T ≤ normalizedFullRelationFirst f hL d V c k n a ⁻¹ᵁ (pullOpen eo W).val)
      (Z : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hZ : ∀ σ, (τ σ).hom ⁻¹ᵁ Z = Z)
      (hZW : Z ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      IsAffineOpen T ∧ IsAffineOpen Z ∧ x ∈ Z ∧ Z ≤ U ∧
      (∀ ι : Fin n ↪ Fin n, Z ≤ subframeMap e o a ι ⁻¹ᵁ T) ∧
      ∃ (u : invariantCoordinates (restrictedAction τ Z hZ))
        (v : invariantCoordinates (restrictedAction
          (normalizedFullRelationAction f hL d V c k n a) T hT)),
        normalizedBoundaryChartMap f hL d V c k n o Z hZ u =
          normalizedOrbitBoundaryCoefficient f hL d V c k n o W Z hZ hZW t ∧
        normalizedBoundaryChartMap f hL d V c k n a T hT v =
          normalizedOrbitBoundaryCoefficient f hL d V c k n a W T hT hTW t ∧
        ∀ ι : Fin n ↪ Fin n,
          ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a Z T).ι ι).ι ≫
            mixedChartFirst o a Z T).appTop u.val =
          ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a Z T).ι ι).ι ≫
            mixedChartSecond o a Z T).appTop v.val := by
  have hn : IsUnit (n.choose n :
      (normalizedFullRelationFrames f hL d V c k n o).presheaf.stalk x) := by
    simp only [Nat.choose_self, Nat.cast_one, isUnit_one]
  obtain ⟨T, hT, hTW, Z, hZ, hZW, haT, haZ, hxZ, hZU, hSel, hNZ, v, hv, hw⟩ :=
    exists_originalSubframe_constructed_unit_lift f hL d V c k n o W U hU n a t x hxU hxW hn
  refine ⟨T, hT, hTW, Z, hZ, hZW, haT, haZ, hxZ, hZU, hSel,
    subframeNormalizedTransfer e o a Z hZ T hT hSel hNZ v, v, hw, hv, ?_⟩
  exact subframeNormalizedTransfer_branches_of_card_eq e o a Z hZ T hT hSel rfl hNZ v

/-- Independent equal-size lifts have an invariant correction solving every original branch. -/
theorem originalSubframe_equal_size_correction
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val)
    (T : (normalizedFullRelationFrames f hL d V c k n a).Opens)
    (hT : ∀ σ, (normalizedFullRelationAction f hL d V c k n a σ).hom ⁻¹ᵁ T = T)
    (hTW : T ≤ normalizedFullRelationFirst f hL d V c k n a ⁻¹ᵁ (pullOpen eo W).val)
    (hSel : ∀ ι : Fin n ↪ Fin n, U ≤ subframeMap e o a ι ⁻¹ᵁ T)
    (u : invariantCoordinates (restrictedAction τ U hU))
    (v : invariantCoordinates (restrictedAction
      (normalizedFullRelationAction f hL d V c k n a) T hT))
    (hu : normalizedBoundaryChartMap f hL d V c k n o U hU u =
      normalizedOrbitBoundaryCoefficient f hL d V c k n o W U hU hUW t)
    (hv : normalizedBoundaryChartMap f hL d V c k n a T hT v =
      normalizedOrbitBoundaryCoefficient f hL d V c k n a W T hT hTW t) :
    ∃ zeta : invariantCoordinates (restrictedAction τ U hU),
      normalizedBoundaryChartMap f hL d V c k n o U hU zeta = 0 ∧
      ∀ ι : Fin n ↪ Fin n,
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U T).ι ι).ι ≫
          mixedChartFirst o a U T).appTop (u - zeta).val =
        ((mixedEmbeddingTestOpen e o a (mixedChartOpen o a U T).ι ι).ι ≫
          mixedChartSecond o a U T).appTop v.val := by
  have hn : IsUnit (n.choose n : Γ(U.toScheme, ⊤)) := by
    simp only [Nat.choose_self, Nat.cast_one, isUnit_one]
  have hdeg : IsUnit ((Fintype.card (Fin n)).choose (Fintype.card (Fin n)) :
      Γ(U.toScheme, ⊤)) := by simpa only [Fintype.card_fin] using hn
  refine ⟨subframeNormalizedCorrection e o a U hU T hT hSel hdeg u v, ?_, ?_⟩
  · exact normalizedOrbitBoundary_subframeNormalizedCorrection_zero
      f hL d V c k n o W U hU hUW n a T hT hSel hTW t hn u v hu hv
  · rw [subframeNormalizedCorrection, sub_sub_cancel]
    exact subframeNormalizedTransfer_branches_of_card_eq e o a U hU T hT hSel rfl hdeg v

end FLT.Mazur.HilbertChart.AffineRestriction
