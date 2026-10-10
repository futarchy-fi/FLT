/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementFamilyComparison

/-!
# Reconstruction of simultaneous affine comparisons

The coherent family comparisons reconstruct the original transport between
the independent covering maps. These squares are the input for identifying
them with the existing pairwise cross-refinement comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinementFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem comparison_square {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {a₀ a₁ a₂ a₃ : A} {b₀ b₁ : B}
    (e₀ : a₀ ≅ a₁) (e₁ : a₁ ≅ a₂) (e₂ : a₃ ≅ a₂)
    (r₀ : F.obj a₀ ≅ b₀) (r₁ : F.obj a₁ ≅ b₀)
    (s₀ : F.obj a₃ ≅ b₁) (s₁ : F.obj a₂ ≅ b₁) (t : b₀ ≅ b₁)
    (h₀ : F.map e₀.hom ≫ r₁.hom = r₀.hom)
    (h₁ : F.map e₁.hom ≫ s₁.hom = r₁.hom ≫ t.hom)
    (h₂ : F.map e₂.hom ≫ s₁.hom = s₀.hom) :
    F.map (e₀ ≪≫ e₁ ≪≫ e₂.symm).hom ≫ s₀.hom = r₀.hom ≫ t.hom := by
  rw [← h₂]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc F e₂.inv e₂.hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, h₁, ← Category.assoc, h₀]


variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type v} {C : ι → Chart p}
variable (ρ : CrossRefinementFamily C) {M : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
attribute [local irreducible] Chart.comparison Chart.reconstruction
  Chart.refinementReconstruction

/-- The common middle comparison reconstructs the original covering-map transport. -/
theorem middleComparison_reconstruction (i j : ι) :
    (pullback (Spec.map ρ.ringMap)).map (ρ.middleComparison D i j).hom ≫
        ((ρ.chart j).reconstruction D).hom =
      ((ρ.chart i).reconstruction D).hom ≫
        (D.transport (ρ.cover i) (ρ.cover j)
          ((ρ.cover_square i).symm.trans (ρ.cover_square j))).hom := by
  unfold middleComparison Chart.reconstruction
  exact D.chartCrossCoverIso_reconstruction ρ.ringMap p ρ.base (ρ.cover i) (ρ.cover j)
    (ρ.cover_square i) (ρ.cover_square j) ρ.faithfullyFlat

/-- The family comparison has the same reconstruction square as a pairwise comparison. -/
theorem effectiveComparison_reconstruction (i j : ι) :
    (pullback (Spec.map ρ.ringMap)).map (ρ.effectiveComparison D i j).hom ≫
        ((C j).refinementReconstruction (ρ.chart j) D (ρ.refinement j)).hom =
      ((C i).refinementReconstruction (ρ.chart i) D (ρ.refinement i)).hom ≫
        (D.transport (ρ.cover i) (ρ.cover j)
          ((ρ.cover_square i).symm.trans (ρ.cover_square j))).hom :=
  comparison_square (pullback (Spec.map ρ.ringMap))
    ((C i).comparison (ρ.chart i) D (ρ.refinement i))
    (ρ.middleComparison D i j)
    ((C j).comparison (ρ.chart j) D (ρ.refinement j))
    ((C i).refinementReconstruction (ρ.chart i) D (ρ.refinement i))
    ((ρ.chart i).reconstruction D)
    ((C j).refinementReconstruction (ρ.chart j) D (ρ.refinement j))
    ((ρ.chart j).reconstruction D)
    (D.transport (ρ.cover i) (ρ.cover j)
      ((ρ.cover_square i).symm.trans (ρ.cover_square j)))
    ((C i).comparison_reconstruction (ρ.chart i) D (ρ.refinement i))
    (ρ.middleComparison_reconstruction D i j)
    ((C j).comparison_reconstruction (ρ.chart j) D (ρ.refinement j))

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinementFamily
