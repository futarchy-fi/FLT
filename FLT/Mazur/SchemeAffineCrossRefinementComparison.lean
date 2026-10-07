/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossCoverDescent
public import FLT.Mazur.SchemeAffineCrossRefinement

/-!
# Effective comparisons on cross refinements of affine charts

Refine each chart using its own map into the cover, then descend the original
cross-cover transport between the two resulting charts. The reconstruction
square retains that transport and characterizes the effective comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
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

variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p} (ρ : C.CrossRefinement C')
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]

/-- Descend transport between the two separate maps of the common affine cover. -/
def middleComparison : ρ.leftChart.sheaf D ≅ ρ.rightChart.sheaf D :=
  D.chartCrossCoverIso ρ.ringMap p ρ.leftChart.base ρ.leftChart.cover ρ.rightChart.cover
    ρ.leftChart.square ρ.rightChart.square ρ.faithfullyFlat

/-- The middle comparison reconstructs the original transport between covering maps. -/
@[reassoc]
theorem middleComparison_reconstruction :
    (pullback (Spec.map ρ.ringMap)).map (ρ.middleComparison D).hom ≫
        (ρ.rightChart.reconstruction D).hom =
      (ρ.leftChart.reconstruction D).hom ≫
        (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over).hom :=
  D.chartCrossCoverIso_reconstruction ρ.ringMap p ρ.leftChart.base
    ρ.leftChart.cover ρ.rightChart.cover ρ.leftChart.square ρ.rightChart.square
    ρ.faithfullyFlat

variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]

/-- Effective comparison of the two original chart sheaves on the common affine base. -/
def effectiveComparison :
    (pullback (Spec.map ρ.leftBase)).obj (C.sheaf D) ≅
      (pullback (Spec.map ρ.rightBase)).obj (C'.sheaf D) :=
  C.comparison ρ.leftChart D ρ.leftRefinement ≪≫ ρ.middleComparison D ≪≫
    (C'.comparison ρ.rightChart D ρ.rightRefinement).symm

attribute [local irreducible] middleComparison Chart.comparison Chart.reconstruction
attribute [local irreducible] Chart.refinementReconstruction

/-- Reconstructing the effective comparison gives the cross-cover descent transport. -/
@[reassoc]
theorem effectiveComparison_reconstruction :
    (pullback (Spec.map ρ.ringMap)).map (ρ.effectiveComparison D).hom ≫
        (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom =
      (C.refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom ≫
        (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over).hom :=
  comparison_square (pullback (Spec.map ρ.ringMap))
    (C.comparison ρ.leftChart D ρ.leftRefinement) (ρ.middleComparison D)
    (C'.comparison ρ.rightChart D ρ.rightRefinement)
    (C.refinementReconstruction ρ.leftChart D ρ.leftRefinement)
    (ρ.leftChart.reconstruction D)
    (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement)
    (ρ.rightChart.reconstruction D)
    (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over)
    (C.comparison_reconstruction ρ.leftChart D ρ.leftRefinement)
    (ρ.middleComparison_reconstruction D)
    (C'.comparison_reconstruction ρ.rightChart D ρ.rightRefinement)

/-- Faithful reconstruction makes the cross-refinement comparison unique. -/
theorem effectiveComparison_unique
    (f : (pullback (Spec.map ρ.leftBase)).obj (C.sheaf D) ⟶
      (pullback (Spec.map ρ.rightBase)).obj (C'.sheaf D))
    (hf : (pullback (Spec.map ρ.ringMap)).map f ≫
        (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement).hom =
      (C.refinementReconstruction ρ.leftChart D ρ.leftRefinement).hom ≫
        (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over).hom) :
    f = (ρ.effectiveComparison D).hom := by
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback ρ.leftBase (C.sheaf D)
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback ρ.rightBase (C'.sheaf D)
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback ρ.leftRefinement.base (C.sheaf D)
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback ρ.rightRefinement.base (C'.sheaf D)
  exact AffineQuasicoherentPullbackFaithful.reconstruction_unique ρ.ringMap
    ρ.faithfullyFlat (C'.refinementReconstruction ρ.rightChart D ρ.rightRefinement) f _
    (hf.trans (ρ.effectiveComparison_reconstruction D).symm)

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
