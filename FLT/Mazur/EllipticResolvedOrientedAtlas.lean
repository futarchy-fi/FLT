/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentAtlas
public import FLT.Mazur.EllipticResolvedComponentLabels
public import FLT.Mazur.EllipticResolvedReciprocalIdentity

/-!
# The complete arithmetic atlas with reciprocal identity and natural labels

Reparametrize only the original identity torus and use the proved finite
component labels. The resulting finite disjoint atlas preserves all original
component images and coefficient maps. No multiplication law is transported
or assumed by this scheme comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ)
local notation "F" => ResidueField A
local notation "p" => resolvedSplitStructure A D
local notation "torus" => Spec (CommRingCat.of (LaurentPolynomial F))
local notation "e" => resolvedComponentIndexEquiv (SplitNodeDepth.depth_pos D)

/-- The existing identity group inversion, and the unchanged orientation on other components. -/
def resolvedComponentOrientation (i : ResolvedComponentIndex depth) : torus ≅ torus := by
  classical
  exact if i = .identity then ProjectiveLine.inversion F else Iso.refl _

/-- The actual arithmetic smooth chart at its natural finite label. -/
def resolvedOrientedComponentChart (i : Fin depth) : torus ⟶ (p).smoothLocus.toScheme :=
  (resolvedComponentOrientation A ((e).symm i)).hom ≫
    resolvedComponentChart A D r ((e).symm i)

instance resolvedOrientedComponentChart_isOpenImmersion (i : Fin depth) :
    IsOpenImmersion (resolvedOrientedComponentChart A D r i) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Finite relabeling and reciprocal orientation retain each complete original component. -/
theorem resolvedOrientedComponentChart_range (i : Fin depth) :
    Set.range (resolvedOrientedComponentChart A D r i) =
      Set.range (resolvedComponentChart A D r ((e).symm i)) :=
  SchemeOpenChartRange.range_iso_comp _ _

/-- Label zero is the actual reciprocal identity chart. -/
theorem resolvedOrientedComponentChart_zero :
    resolvedOrientedComponentChart A D r ⟨0, D.depth_pos⟩ =
      resolvedReciprocalIdentitySmoothChart A D := by
  have h0 : (e).symm ⟨0, D.depth_pos⟩ = .identity := by
    apply (e).injective
    rw [Equiv.apply_symm_apply]
    rfl
  simp only [resolvedOrientedComponentChart, h0, resolvedComponentOrientation, ite_true,
    resolvedComponentChart, resolvedReciprocalIdentitySmoothChart]

/-- Every finite-labeled chart preserves the original residue-field map. -/
@[reassoc] theorem resolvedOrientedComponentChart_structure (i : Fin depth) :
    resolvedOrientedComponentChart A D r i ≫ (p).smoothLocus.ι ≫ p =
      (MultiplicativeGroupScheme.gm F).hom := by
  rw [resolvedOrientedComponentChart, Category.assoc, resolvedComponentChart_structure]
  by_cases hi : (e).symm i = .identity
  · rw [resolvedComponentOrientation, ite_eq_left hi, ← PolygonSplitGroup.reciprocalGroupIso_left]
    exact (PolygonSplitGroup.reciprocalGroupIso F).hom.hom.hom.hom.w
  · rw [resolvedComponentOrientation, ite_eq_right hi, Iso.refl_hom, Category.id_comp]

/-- The finite-labeled reciprocal atlas covers the whole actual smooth fiber. -/
theorem resolvedOrientedComponentCharts_cover (z : (p).smoothLocus.toScheme) :
    ∃ i, z ∈ Set.range (resolvedOrientedComponentChart A D r i) := by
  obtain ⟨j, hj⟩ := resolvedComponentCharts_cover A D r z
  refine ⟨(e) j, ?_⟩
  rwa [resolvedOrientedComponentChart_range, Equiv.symm_apply_apply]

/-- Different finite labels have disjoint original component images. -/
theorem resolvedOrientedComponentCharts_disjoint (i j : Fin depth) (hij : i ≠ j) :
    Disjoint (Set.range (resolvedOrientedComponentChart A D r i))
      (Set.range (resolvedOrientedComponentChart A D r j)) := by
  rw [resolvedOrientedComponentChart_range, resolvedOrientedComponentChart_range]
  exact resolvedComponentCharts_disjoint A D r _ _ (fun h => hij ((e).symm.injective h))

/-- The finite naturally labeled torus coproduct maps to the actual smooth fiber. -/
def resolvedOrientedAtlasMap : (∐ fun _ : Fin depth => torus) ⟶ (p).smoothLocus.toScheme :=
  Sigma.desc (resolvedOrientedComponentChart A D r)

/-- The complete comparison retains each finite-labeled oriented chart. -/
@[reassoc] theorem resolvedOrientedAtlasMap_chart (i : Fin depth) :
    Sigma.ι (fun _ : Fin depth => torus) i ≫ resolvedOrientedAtlasMap A D r =
      resolvedOrientedComponentChart A D r i := Sigma.ι_comp_desc _ _

instance resolvedOrientedAtlasMap_isOpenImmersion :
    IsOpenImmersion (resolvedOrientedAtlasMap A D r) := by
  apply isOpenImmersion_sigmaDesc
  intro i j hij
  exact resolvedOrientedComponentCharts_disjoint A D r i j hij

instance resolvedOrientedAtlasMap_isIso : IsIso (resolvedOrientedAtlasMap A D r) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨i, x, rfl⟩ := resolvedOrientedComponentCharts_cover A D r z
  exact ⟨Sigma.ι (fun _ : Fin depth => torus) i x,
    congrArg (fun f => f x) (resolvedOrientedAtlasMap_chart A D r i)⟩

/-- The full actual smooth fiber has the naturally labeled reciprocal arithmetic atlas. -/
def resolvedOrientedAtlasIso : (∐ fun _ : Fin depth => torus) ≅ (p).smoothLocus.toScheme :=
  asIso (resolvedOrientedAtlasMap A D r)

/-- The entire finite atlas comparison retains the original coefficient map. -/
@[reassoc] theorem resolvedOrientedAtlasMap_structure :
    resolvedOrientedAtlasMap A D r ≫ (p).smoothLocus.ι ≫ p =
      Sigma.desc (fun _ : Fin depth => (MultiplicativeGroupScheme.gm F).hom) := by
  apply Sigma.hom_ext
  intro i
  rw [resolvedOrientedAtlasMap_chart_assoc, Sigma.ι_comp_desc]
  exact resolvedOrientedComponentChart_structure A D r i

end FLT.Mazur.WeierstrassDividedDepth
