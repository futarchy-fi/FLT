/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeDenominatorCover
public import FLT.Mazur.PolygonCanonicalChartRing

/-!
# Algebra compatibility of the actual localized node chart maps

Both affine node charts and their exact principal refinements are over K.
Consequently the canonical projective ring maps preserve the given scalars.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonNodeAffineCharts
open PolygonPinching PolygonNodeEqualizer PolygonNodePresentation
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The split-node chart preserves its standard K structure. -/
lemma splitChart_toBase (hn₂ : 2 ≤ n) (i : Fin n) :
    splitChart K n hn p q h hn₂ i ≫ C.hom = aToBase K := by
  unfold splitChart
  simp only [Category.assoc, Over.w]
  exact PolygonCyclicAtlas.chart_toBase K n hn₂ i

/-- Principal localization preserves the structure map of any affine K chart. -/
lemma refinement_toBase {R : Type u} [CommRing R] [Algebra K R]
    {X : Scheme.{u}} (j : Spec (.of R) ⟶ X) (b : X ⟶ Spec (.of K))
    (hj : j ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K R))) (s : R) :
    PrincipalAffineRefinement.chart j s ≫ b =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away s))) := by
  rw [PrincipalAffineRefinement.chart, Category.assoc, hj,
    PrincipalAffineRefinement.inclusion, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq K R (Localization.Away s)]

/-- The exact split denominator chart has the standard localization algebra. -/
lemma splitDenominatorChart_toBase (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n)
    (x : Spec (.of K)) :
    splitDenominatorChart K n hn p q h a hn₂ i x ≫ C.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K
        (Localization.Away (splitDenominator K n hn p q h a hn₂ i x)))) :=
  refinement_toBase K _ _ (splitChart_toBase K n hn p q h hn₂ i) _

end PolygonNodeAffineCharts
namespace PolygonNodeAffineCharts
open PolygonPinching PolygonNodePresentation
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)

/-- The self-pinched chart preserves the actual equal-endpoint algebra structure. -/
lemma oneChart_toBase : oneChart K hn p q h ≫ C.hom = bToBase K := by
  unfold oneChart
  simp only [Category.assoc, Over.w]
  exact OneGonGluing.node_toBase K

/-- The chosen B localization also retains its standard K structure. -/
lemma oneDenominatorChart_toBase (a : Fin 1 → Kˣ) (x : Spec (.of K)) :
    oneDenominatorChart K hn p q h a x ≫ C.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K
        (Localization.Away (oneDenominator K hn p q h a x)))) :=
  refinement_toBase K _ _ (oneChart_toBase K hn p q h) _

end PolygonNodeAffineCharts
namespace PolygonCubicSections
open PolygonPinching
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)
  {R : Type u} [CommRing R] [Algebra K R] (j : Spec (.of R) ⟶ C.left)
  [IsOpenImmersion j] (hj : Set.range j ⊆ divisorComplement K n p a)
  (hb : j ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap K R)))

include hb in
/-- Geometric scalar compatibility is compatibility with the existing K algebras. -/
lemma affineCanonicalChartRingMap_algebraMap (b : K) :
    affineCanonicalChartRingMap K n hn p q h a j hj
      (algebraMap K (ProjectiveSpace.chartRing K _ (canonicalIndex.{u} n)) b) =
        algebraMap K R b := by
  rw [show algebraMap K (ProjectiveSpace.chartRing K _ (canonicalIndex.{u} n)) =
    ProjectiveSpace.chartScalars K _ (canonicalIndex.{u} n) from rfl,
    affineCanonicalChartRingMap_scalar, hb]
  have he := congrArg (fun f ↦ f.hom ((Scheme.ΓSpecIso (.of K)).inv b))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap K R)))
  change (Scheme.ΓSpecIso (.of R)).hom
    ((Spec.map (CommRingCat.ofHom (algebraMap K R))).appTop
      ((Scheme.ΓSpecIso (.of K)).inv b)) =
    algebraMap K R ((Scheme.ΓSpecIso (.of K)).hom ((Scheme.ΓSpecIso (.of K)).inv b)) at he
  rw [show (Scheme.ΓSpecIso (.of K)).hom ((Scheme.ΓSpecIso (.of K)).inv b) = b from
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.apply_symm_apply b] at he
  exact he

/-- The same actual chart map, bundled as a K-algebra homomorphism. -/
def affineCanonicalChartAlgHom :
    ProjectiveSpace.chartRing K _ (canonicalIndex.{u} n) →ₐ[K] R :=
  ⟨affineCanonicalChartRingMap K n hn p q h a j hj,
    affineCanonicalChartRingMap_algebraMap K n hn p q h a j hj hb⟩

end FLT.Mazur.PolygonCubicSections
