/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentSeparation
public import FLT.Mazur.EllipticResolvedZeroStageCoverage

/-!
# The full actual arithmetic component atlas

The disjoint arithmetic tori form an open cover and their coproduct is the
entire original smooth resolved fiber. This scheme isomorphism preserves
every original chart and coefficient map, without a surjectivity claim for
specialization of arithmetic points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ)
local notation "F" => ResidueField A
local notation "torus" => Spec (CommRingCat.of (LaurentPolynomial F))
local notation "p" => resolvedSplitStructure A D
local notation "chart" => resolvedComponentChart A D r
local notation "family" => fun (_ : ResolvedComponentIndex depth) => torus

/-- The full arithmetic torus family is an open cover of the actual smooth fiber. -/
def resolvedComponentOpenCover : (p).smoothLocus.toScheme.OpenCover where
  I₀ := ResolvedComponentIndex depth
  X _ := torus
  f := chart
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨resolvedComponentCharts_cover A D r, fun _ => inferInstance⟩

/-- Every geometric smooth point lies on exactly one original arithmetic torus. -/
theorem resolvedComponentChart_unique (z : (p).smoothLocus.toScheme) :
    ∃! i, z ∈ Set.range (chart i) := by
  obtain ⟨i, hi⟩ := resolvedComponentCharts_cover A D r z
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra hji
  exact Set.disjoint_left.mp (resolvedComponentCharts_disjoint A D r j i hji) hj hi

/-- The actual arithmetic component coproduct maps into the original resolved smooth fiber. -/
def resolvedComponentAtlasMap : (∐ family) ⟶ (p).smoothLocus.toScheme := Sigma.desc chart

/-- The coproduct map retains each original arithmetic torus without reparametrization. -/
@[reassoc] theorem resolvedComponentAtlasMap_chart (i : ResolvedComponentIndex depth) :
    Sigma.ι family i ≫ resolvedComponentAtlasMap A D r = chart i := Sigma.ι_comp_desc _ _

instance resolvedComponentAtlasMap_isOpenImmersion :
    IsOpenImmersion (resolvedComponentAtlasMap A D r) := by
  apply isOpenImmersion_sigmaDesc
  intro i j hij
  exact resolvedComponentCharts_disjoint A D r i j hij

/-- Every geometric point is in the arithmetic component coproduct image. -/
theorem resolvedComponentAtlasMap_surjective :
    Function.Surjective (resolvedComponentAtlasMap A D r) := by
  intro z
  obtain ⟨i, x, rfl⟩ := resolvedComponentCharts_cover A D r z
  refine ⟨Sigma.ι family i x, ?_⟩
  exact congrArg (fun f => f x) (resolvedComponentAtlasMap_chart A D r i)

instance resolvedComponentAtlasMap_isIso : IsIso (resolvedComponentAtlasMap A D r) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  exact (resolvedComponentAtlasMap_surjective A D r).range_eq

/-- The full smooth resolved fiber is the disjoint union of its actual arithmetic tori. -/
def resolvedComponentAtlasIso : (∐ family) ≅ (p).smoothLocus.toScheme :=
  asIso (resolvedComponentAtlasMap A D r)

/-- The coproduct comparison retains the original residue-field structure map. -/
@[reassoc] theorem resolvedComponentAtlasMap_structure :
    resolvedComponentAtlasMap A D r ≫ (p).smoothLocus.ι ≫ p =
      Sigma.desc (fun _ : ResolvedComponentIndex depth =>
        (MultiplicativeGroupScheme.gm F).hom) := by
  apply Sigma.hom_ext
  intro i
  rw [resolvedComponentAtlasMap_chart_assoc, Sigma.ι_comp_desc]
  exact resolvedComponentChart_structure A D r i

/-- The full disjoint atlas comparison also lives over the original residue spectrum. -/
def resolvedComponentAtlasOverIso :
    Over.mk (Sigma.desc (fun _ : ResolvedComponentIndex depth =>
      (MultiplicativeGroupScheme.gm F).hom)) ≅ Over.mk ((p).smoothLocus.ι ≫ p) :=
  Over.isoMk (resolvedComponentAtlasIso A D r) (resolvedComponentAtlasMap_structure A D r)

end FLT.Mazur.WeierstrassDividedDepth
