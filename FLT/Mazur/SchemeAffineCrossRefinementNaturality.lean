/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossCoverNaturality

/-!
# Naturality of effective cross-refinement comparisons

The two genuine chart refinements and the middle cross-cover comparison
intertwine compatible original maps, hence so does their composite.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem triple_naturality {B : Type*} [Category B]
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : B}
    (e₀ : a₀ ≅ b₀) (e₁ : a₁ ≅ b₁) (m₀ : b₀ ≅ c₀) (m₁ : b₁ ≅ c₁)
    (r₀ : d₀ ≅ c₀) (r₁ : d₁ ≅ c₁)
    (f : a₀ ⟶ a₁) (g : b₀ ⟶ b₁) (h : c₀ ⟶ c₁) (k : d₀ ⟶ d₁)
    (he : f ≫ e₁.hom = e₀.hom ≫ g) (hm : g ≫ m₁.hom = m₀.hom ≫ h)
    (hr : k ≫ r₁.hom = r₀.hom ≫ h) :
    f ≫ (e₁ ≪≫ m₁ ≪≫ r₁.symm).hom = (e₀ ≪≫ m₀ ≪≫ r₀.symm).hom ≫ k := by
  apply (cancel_mono r₁.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [hr, Iso.inv_hom_id_assoc, ← Category.assoc f e₁.hom, he, Category.assoc, hm]

variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p} (ρ : C.CrossRefinement C')
variable {M N : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (E : SchemeGeometricDescent.Data p N)
variable [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.leftChart.cover).obj N).IsQuasicoherent]
variable [((pullback ρ.rightChart.cover).obj N).IsQuasicoherent]
attribute [local irreducible] Chart.sheaf Chart.map Chart.comparison middleComparison

/-- Middle comparisons preserve every compatible map of the original descent objects. -/
@[reassoc]
theorem middleComparison_naturality (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    ρ.leftChart.map D E f hf ≫ (ρ.middleComparison E).hom =
      (ρ.middleComparison D).hom ≫ ρ.rightChart.map D E f hf := by
  simpa only [Chart.map, Chart.sheaf, middleComparison, leftChart, rightChart] using
    D.chartCrossCoverIso_naturality ρ.ringMap p E ρ.leftChart.base
    ρ.leftChart.cover ρ.rightChart.cover ρ.leftChart.square ρ.rightChart.square
    ρ.faithfullyFlat f hf

variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [((pullback C.cover).obj N).IsQuasicoherent]
variable [((pullback C'.cover).obj N).IsQuasicoherent]

/-- The complete effective comparison is natural for compatible original maps. -/
@[reassoc]
theorem effectiveComparison_naturality (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    (pullback (Spec.map ρ.leftBase)).map (C.map D E f hf) ≫
        (ρ.effectiveComparison E).hom =
      (ρ.effectiveComparison D).hom ≫
        (pullback (Spec.map ρ.rightBase)).map (C'.map D E f hf) := by
  exact triple_naturality
    (C.comparison ρ.leftChart D ρ.leftRefinement)
    (C.comparison ρ.leftChart E ρ.leftRefinement)
    (ρ.middleComparison D) (ρ.middleComparison E)
    (C'.comparison ρ.rightChart D ρ.rightRefinement)
    (C'.comparison ρ.rightChart E ρ.rightRefinement) _ _ _ _
    (C.comparison_naturality ρ.leftChart D E ρ.leftRefinement f hf)
    (ρ.middleComparison_naturality D E f hf)
    (C'.comparison_naturality ρ.rightChart D E ρ.rightRefinement f hf)

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
