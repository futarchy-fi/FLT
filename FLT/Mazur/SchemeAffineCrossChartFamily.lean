/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossCoverCoherence
public import FLT.Mazur.SchemeAffineChartReconstruction

/-!
# Families of affine chart refinements with independent covering maps

A common affine base and faithfully flat cover can refine many original charts
using different maps into Y. This geometric family constructs comparisons of
the original descended sheaves on that base; no common map into Y is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u} (C : ι → Chart p)

/-- Geometric refinements with common affine rings and independently mapped cover charts. -/
structure CrossChartFamily where
  /-- The common base ring. -/
  baseRing : CommRingCat.{u}
  /-- The ring of its chosen cover. -/
  coverRing : CommRingCat.{u}
  /-- The common affine covering map. -/
  ringMap : baseRing ⟶ coverRing
  /-- Faithful flatness of the common covering map. -/
  faithfullyFlat : ringMap.hom.FaithfullyFlat
  /-- The common map into the original base. -/
  base : Spec baseRing ⟶ X
  /-- Restrictions of the original base charts. -/
  baseMap : ∀ i, (C i).baseRing ⟶ baseRing
  /-- Separate restrictions of the original covering charts. -/
  coverMap : ∀ i, (C i).coverRing ⟶ coverRing
  /-- The coordinate squares commute. -/
  square : ∀ i, (C i).ringMap ≫ coverMap i = baseMap i ≫ ringMap
  /-- Each base restriction gives the common map into X. -/
  base_over : ∀ i, Spec.map (baseMap i) ≫ (C i).base = base

namespace CrossChartFamily
variable {C} (F : CrossChartFamily C)

/-- The refined chart carrying the ith actual map into the original cover. -/
def chart (i : ι) : Chart p where
  baseRing := F.baseRing
  coverRing := F.coverRing
  ringMap := F.ringMap
  faithfullyFlat := F.faithfullyFlat
  base := F.base
  cover := Spec.map (F.coverMap i) ≫ (C i).cover
  square := by
    rw [← F.base_over i]
    exact SchemeGeometricDescent.Data.affineChart_composite_square
      (C i).ringMap F.ringMap (F.baseMap i) (F.coverMap i) (F.square i) p
      (C i).base (C i).cover (C i).square

/-- Each common chart is a genuine geometric refinement of its original chart. -/
def refinement (i : ι) : (C i).Refinement (F.chart i) where
  base := F.baseMap i
  cover := F.coverMap i
  square := F.square i
  base_over := F.base_over i
  cover_over := rfl

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (F.chart i).cover).obj M).IsQuasicoherent]

/-- The effective middle comparison between the independent common covering maps. -/
def middle (i j : ι) : (F.chart i).sheaf D ≅ (F.chart j).sheaf D :=
  D.chartCrossCoverIso F.ringMap p F.base (F.chart i).cover (F.chart j).cover
    (F.chart i).square (F.chart j).square F.faithfullyFlat

/-- Middle comparisons compose by the original descent cocycle. -/
@[reassoc]
theorem middle_comp (i j k : ι) :
    (F.middle D i j).hom ≫ (F.middle D j k).hom = (F.middle D i k).hom :=
  D.chartCrossCoverIso_comp F.ringMap p F.base (F.chart i).cover (F.chart j).cover
    (F.chart k).cover (F.chart i).square (F.chart j).square (F.chart k).square
    F.faithfullyFlat

/-- A middle self-comparison is the identity. -/
@[simp]
theorem middle_self (i : ι) : F.middle D i i = Iso.refl _ :=
  D.chartCrossCoverIso_self F.ringMap p F.base (F.chart i).cover (F.chart i).square
    F.faithfullyFlat

variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]

/-- Comparison of original descended sheaves on the common affine base. -/
def transition (i j : ι) :
    (pullback (Spec.map (F.baseMap i))).obj ((C i).sheaf D) ≅
      (pullback (Spec.map (F.baseMap j))).obj ((C j).sheaf D) :=
  (C i).comparison (F.chart i) D (F.refinement i) ≪≫ F.middle D i j ≪≫
    ((C j).comparison (F.chart j) D (F.refinement j)).symm

attribute [local irreducible] Chart.comparison middle

/-- The actual cross-cover transitions satisfy the cocycle on this common affine base. -/
@[reassoc]
theorem transition_comp (i j k : ι) :
    (F.transition D i j).hom ≫ (F.transition D j k).hom =
      (F.transition D i k).hom := by
  simp only [transition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  erw [F.middle_comp_assoc D i j k]

/-- The actual transition from a chart to itself is the identity. -/
@[simp]
theorem transition_self (i : ι) : F.transition D i i = Iso.refl _ := by
  apply Iso.ext
  simp only [transition, Iso.trans_hom, Iso.symm_hom, middle_self, Iso.refl_hom,
    Category.id_comp, Iso.hom_inv_id]

end CrossChartFamily
end FLT.Mazur.SchemeAffineDescent
