/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBranchKernel
public import FLT.Mazur.PolygonInfinitesimalEdgeExt
public import FLT.Mazur.PolygonInfinitesimalFamily

/-!
# Closed factorization is detected on all full polygon edges

The original node cover and its two-branch kernel test propagate ideal
containment from the Laurent edges to the entire nonreduced polygon.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n)
  [TopologicalSpace.NoetherianSpace (scheme R t n h)]
  [TopologicalSpace.NoetherianSpace (PolygonSmoothing.chart R t)]

/-- Full Laurent edges detect the entire ideal kernel, including every node nilpotent. -/
theorem le_kernel_of_edges {Y : Scheme} (f : scheme R t n h ⟶ Y)
    (I : Y.IdealSheafData) (he : ∀ i, I ≤ (edge R t n h i ≫ f).ker) : I ≤ f.ker := by
  let _ : QuasiCompact f := quasiCompact_of_noetherianSpace_source _
  rw [← Scheme.Hom.iInf_ker_openCover_map_comp f (chartCover R t n h)]
  apply le_iInf
  intro i
  change I ≤ (chart R t n h i ≫ f).ker
  apply le_kernel_of_branches t
  · simpa only [edge, Category.assoc] using he i
  · have ho : precedingBranch R t ≫ chart R t n h i =
        edge R t n h (finRotate n i) := by
      simpa only [Equiv.symm_apply_apply, edge] using
        (overlap R t n h (finRotate n i)).symm
    have hx := he (finRotate n i)
    rw [← ho, Category.assoc] at hx
    change I ≤ ((edgeInversion R).hom ≫ rightBranchOpen R t ≫
      chart R t n h i ≫ f).ker at hx
    rwa [Scheme.Hom.ker_comp_of_isIso] at hx

/-- Actual lifts on all full edges construct a map through a closed subscheme. -/
def closedLiftOfEdges {Y Z : Scheme} (j : Z ⟶ Y) [IsClosedImmersion j]
    (f : scheme R t n h ⟶ Y)
    (g : Fin n → (PolygonSmoothing.branchTorus R ⟶ Z))
    (hg : ∀ i, g i ≫ j = edge R t n h i ≫ f) : scheme R t n h ⟶ Z :=
  IsClosedImmersion.lift j f (le_kernel_of_edges R t n h f j.ker fun i ↦ by
    rw [← hg i]
    exact (g i).le_ker_comp j)

/-- The closed lift retains the original map on the whole polygon. -/
@[reassoc] theorem closedLiftOfEdges_fac {Y Z : Scheme} (j : Z ⟶ Y) [IsClosedImmersion j]
    (f : scheme R t n h ⟶ Y)
    (g : Fin n → (PolygonSmoothing.branchTorus R ⟶ Z))
    (hg : ∀ i, g i ≫ j = edge R t n h i ≫ f) :
    closedLiftOfEdges R t n h j f g hg ≫ j = f := IsClosedImmersion.lift_fac _ _ _

end FLT.Mazur.PolygonInfinitesimal
