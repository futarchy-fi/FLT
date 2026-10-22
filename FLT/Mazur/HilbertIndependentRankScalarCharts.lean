/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationIndependentAffineLifts
public import FLT.Mazur.HilbertNormalizedStableAffine
public import FLT.Mazur.HilbertPrescribedScalarMorphism
public import FLT.Mazur.RelativeDoubleRankThickenings

/-!
# Independent rank charts on the original Hilbert scalar kernel pair

The scalar kernel pair has no assumed original arrow. Restricting both ranks
constructs two actual stable affine frame charts over the original section
ring, on a common etale coefficient neighborhood at every pair of orders.
The original scalar morphisms agree; fullness of their images is not claimed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples RelativeRelationOrbit SchemeScalarPrincipalNeighborhood
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
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
variable (O : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo O).val
local notation "σ" => scalarMorphism (orbitScalarCoordinates eo O)
local notation "x" => pullback.fst σ σ ≫ (E).ι
local notation "y" => pullback.snd σ σ ≫ (E).ι
local instance independentHilbertOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance independentHilbertOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance independentHilbertOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- All independent scalar tests have affine rank charts preserving the original scalars. -/
theorem exists_scalarKernel_doubleRank_affine_charts (n m r s : ℕ) (o : Fin n) (o' : Fin m)
    (z : doubleRankThickening (Over.mk p) x y n m r s) :
    ∃ (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (W : (normalizedFullRelationFrames f hL d V c k m o').Opens)
      (T : Scheme.{0}) (a : T ⟶ U.toScheme) (b : T ⟶ W.toScheme)
      (v : T ⟶ doubleRankThickening (Over.mk p) x y n m r s) (t : T)
      (hU : ∀ g, (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U)
      (hW : ∀ g, (normalizedFullRelationAction f hL d V c k m o' g).hom ⁻¹ᵁ W = W)
      (hUO : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E)
      (hWO : W ≤ normalizedFullRelationFirst f hL d V c k m o' ⁻¹ᵁ E),
      IsAffineOpen U ∧ IsAffineOpen W ∧ IsAffine T ∧ Etale v ∧ v t = z ∧
      a ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o =
        v ≫ doubleRankMap (Over.mk p) x y n m r s ≫ x ∧
      b ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' =
        v ≫ doubleRankMap (Over.mk p) x y n m r s ≫ y ∧
      a ≫ scalarMorphism (invariantScalarCoordinates
        (restrictedAction (normalizedFullRelationAction f hL d V c k n o) U hU)
        (normalizedOriginalScalarMap f hL d V c k n o O U hU hUO)) =
      b ≫ scalarMorphism (invariantScalarCoordinates
        (restrictedAction (normalizedFullRelationAction f hL d V c k m o') W hW)
        (normalizedOriginalScalarMap f hL d V c k m o' O W hW hWO)) := by
  let l := doubleRankMap (Over.mk p) x y n m r s
  let _ := finTuples_affine (firstRelationEnvelope (A := A) V) n
  let _ := finTuples_affine (firstRelationEnvelope (A := A) V) m
  obtain ⟨U, W, T, a, b, v, t, hUaff, hWaff, hT, hv, ht, hUO, hWO,
      hU, hW, ha, hb⟩ := exists_independent_affine_endpoint_lifts e n m o o'
    (normalizedOriginalFrameInclusion f hL d V c k n o)
    (fullRelationOrderedEnvelopeMap f hL d V c k n)
    (normalizedOriginalFrameInclusion f hL d V c k m o')
    (fullRelationOrderedEnvelopeMap f hL d V c k m) (l ≫ x) (l ≫ y)
    E (pullOpen_preimage_eq eo O)
    (by rintro _ ⟨w, rfl⟩; exact (doubleRankMap_endpoints (Over.mk p) x y n m r s w).1)
    (by rintro _ ⟨w, rfl⟩; exact (doubleRankMap_endpoints (Over.mk p) x y n m r s w).2)
    z (pullback.fst σ σ (l z)).property (pullback.snd σ σ (l z)).property
  change a ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o = v ≫ l ≫ x at ha
  change b ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' = v ≫ l ≫ y at hb
  have ha' : a ≫ (normalizedFullRelationFirst f hL d V c k n o).resLE E U hUO =
      v ≫ l ≫ pullback.fst σ σ := by
    apply (cancel_mono (E).ι).mp
    simpa only [Category.assoc, Scheme.Hom.resLE_comp_ι] using ha
  have hb' : b ≫ (normalizedFullRelationFirst f hL d V c k m o').resLE E W hWO =
      v ≫ l ≫ pullback.snd σ σ := by
    apply (cancel_mono (E).ι).mp
    simpa only [Category.assoc, Scheme.Hom.resLE_comp_ι] using hb
  refine ⟨U, W, T, a, b, v, t, hU, hW, hUO, hWO, hUaff, hWaff, hT, hv, ht,
    ha, hb, ?_⟩
  rw [normalizedSource_scalarMorphism_factor, normalizedSource_scalarMorphism_factor,
    ← Category.assoc a, ha', ← Category.assoc b, hb']
  simp only [Category.assoc, pullback.condition]

end FLT.Mazur.HilbertChart.AffineRestriction
