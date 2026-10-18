/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertLabelResidualLifts
public import FLT.Mazur.HilbertFiniteLabelRefinement

/-!
# Construct exact local lifts inside finite independent labelled chart families

At every common transported point, construct the stable affine chart inside all
supplied domains, then lift the original boundary section simultaneously on its
labelled copies. No common affine chart is required as input. The construction
solves full-size embedding stages locally, leaving strict subframes and residuals.
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
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (n : ℕ) (o : Fin n)
local notation "τ" => normalizedFullRelationAction f hL d V c k n o
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Local common affine geometry and simultaneous original-boundary lifts are constructed. -/
theorem exists_originalFiniteLabel_embedding_lifts
    {T : Type} [Finite T] (a : T → Fin n)
    (Us : (v : T) → (normalizedFullRelationFrames f hL d V c k n (a v)).Opens)
    (hUs : ∀ v σ,
      (normalizedFullRelationAction f hL d V c k n (a v) σ).hom ⁻¹ᵁ Us v = Us v)
    (x : normalizedFullRelationFrames f hL d V c k n o)
    (hxW : normalizedFullRelationFirst f hL d V c k n o x ∈ (pullOpen eo W).val)
    (hx : ∀ v, labelChange e (Fin n) o (a v) x ∈ Us v) :
    ∃ (Z : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (hZ : ∀ σ, (τ σ).hom ⁻¹ᵁ Z = Z)
      (hZW : Z ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val),
      IsAffineOpen Z ∧ x ∈ Z ∧ (∀ v, labelChange e (Fin n) (a v) o ⁻¹ᵁ Z ≤ Us v) ∧
      let Zs := fun v ↦ labelChange e (Fin n) (a v) o ⁻¹ᵁ Z
      let hs := fun v ↦ label_preimage_stable e (Fin n) (a v) o Z hZ
      ∃ v : ∀ idx, invariantCoordinates
          (restrictedAction (normalizedFullRelationAction f hL d V c k n (a idx))
            (Zs idx) (hs idx)),
        (∀ idx, normalizedBoundaryChartMap f hL d V c k n (a idx) (Zs idx) (hs idx) (v idx) =
          normalizedOrbitBoundaryCoefficient f hL d V c k n (a idx) W (Zs idx) (hs idx)
            (normalizedLabelRefinement_domain f hL d V c k n o W Z hZW
              (a idx) (Zs idx) le_rfl) t) ∧
        ∀ idx l (ι : Fin n ↪ Fin n),
          ((MixedFrames.mixedEmbeddingTestOpen e (a idx) (a l)
            (MixedFrames.mixedChartOpen (a idx) (a l) (Zs idx) (Zs l)).ι ι).ι ≫
            MixedFrames.mixedChartFirst (a idx) (a l) (Zs idx) (Zs l)).appTop (v idx).val =
          ((MixedFrames.mixedEmbeddingTestOpen e (a idx) (a l)
            (MixedFrames.mixedChartOpen (a idx) (a l) (Zs idx) (Zs l)).ι ι).ι ≫
            MixedFrames.mixedChartSecond (a idx) (a l) (Zs idx) (Zs l)).appTop (v l).val := by
  obtain ⟨Z, ha, hxZ, hZW, hZ, hZs⟩ := exists_normalized_finite_label_refinement
    f hL d V c k n o (pullOpen eo W).val (pullOpen_preimage_eq eo W) a Us hUs x hxW hx
  refine ⟨Z, hZ, hZW, ha, hxZ, hZs, ?_⟩
  exact exists_originalLabel_embedding_lifts f hL d V c k n o W Z hZ hZW t ha a
    (fun idx ↦ labelChange e (Fin n) (a idx) o ⁻¹ᵁ Z)
    (fun idx ↦ label_preimage_stable e (Fin n) (a idx) o Z hZ) (fun _ ↦ le_rfl)

end FLT.Mazur.HilbertChart.AffineRestriction
