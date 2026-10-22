/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIndependentRankScalarCharts
public import FLT.Mazur.EquivalenceRelationPositiveExactRank

/-!
# Every original scalar kernel point has independent affine rank lifts

The actual identity arrows supply both distinguished labels, so no rank or
label hypotheses remain on scalar kernel points. Every pair of infinitesimal
orders is retained. The etale coefficient extension is over its rank stage;
the stage map to the original kernel pair is not asserted to be flat.
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
local instance fullScalarRankOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance fullScalarRankOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance fullScalarRankOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- The concrete Hilbert geometry proves finiteness of both full sources on every two-rank stage. -/
theorem scalarKernel_doubleRank_sources_finite (n m r s : ℕ) :
    IsFinite (pullback.snd p (doubleRankMap (Over.mk p) x y n m r s ≫ x)) ∧
      IsFinite (pullback.snd p (doubleRankMap (Over.mk p) x y n m r s ≫ y)) := by
  let _ : LocallyQuasiFinite p :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
  let _ : LocallyQuasiFinite (Over.mk p).hom := inferInstanceAs (LocallyQuasiFinite p)
  exact doubleRank_both_sources_finite (Over.mk p) x y n m r s

/-- Every original scalar kernel point has two affine normalized lifts at every pair of orders. -/
theorem exists_scalarKernel_point_affine_rank_lifts (r s : ℕ) (z : (pullback σ σ : Scheme)) :
    ∃ (n m : ℕ) (o : Fin n) (o' : Fin m)
      (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
      (W : (normalizedFullRelationFrames f hL d V c k m o').Opens)
      (T : Scheme.{0}) (a : T ⟶ U.toScheme) (b : T ⟶ W.toScheme)
      (v : T ⟶ doubleRankThickening (Over.mk p) x y n m r s) (t : T),
      IsAffineOpen U ∧ IsAffineOpen W ∧ IsAffine T ∧ Etale v ∧
      doubleRankMap (Over.mk p) x y n m r s (v t) = z ∧
      (∀ g, (normalizedFullRelationAction f hL d V c k n o g).hom ⁻¹ᵁ U = U) ∧
      (∀ g, (normalizedFullRelationAction f hL d V c k m o' g).hom ⁻¹ᵁ W = W) ∧
      U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ E ∧
      W ≤ normalizedFullRelationFirst f hL d V c k m o' ⁻¹ᵁ E ∧
      a ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o =
        v ≫ doubleRankMap (Over.mk p) x y n m r s ≫ x ∧
      b ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' =
        v ≫ doubleRankMap (Over.mk p) x y n m r s ≫ y := by
  obtain ⟨n, m, w, hw⟩ := exists_doubleRank_lift (Over.mk p) x y r s z
  obtain ⟨⟨o⟩, ⟨o'⟩⟩ := doubleRank_nonempty_labels e x y n m r s w
  obtain ⟨U, W, T, a, b, v, t, hU, hW, hUO, hWO, hUaff, hWaff, hT, hv, ht,
      ha, hb, _⟩ := exists_scalarKernel_doubleRank_affine_charts
    f hL d V c k O n m r s o o' w
  exact ⟨n, m, o, o', U, W, T, a, b, v, t, hUaff, hWaff, hT, hv,
    (congrArg (doubleRankMap (Over.mk p) x y n m r s) ht).trans hw,
    hU, hW, hUO, hWO, ha, hb⟩

end FLT.Mazur.HilbertChart.AffineRestriction
