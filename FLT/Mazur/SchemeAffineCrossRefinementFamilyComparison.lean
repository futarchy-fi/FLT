/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementFamily
public import FLT.Mazur.SchemeAffineCrossCoverCocycle

/-!
# Effective comparisons for a simultaneous affine refinement

The common charts have one named affine base and independent covering maps.
Effective cross-cover descent compares them coherently; conjugating by the
original chart comparisons gives a cocycle on the original pulled-back sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinementFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type v} {C : ι → Chart p}
variable (ρ : CrossRefinementFamily C) {M : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]

/-- The independent common-cover maps preserve quasicoherence. -/
instance cover_isQuasicoherent (i : ι) :
    ((pullback (ρ.cover i)).obj M).IsQuasicoherent :=
  SchemeGeometricDescent.Data.isQuasicoherent_compositeChartPullback
    (ρ.coverMap i) (C i).cover

/-- Descend transport between two of the independent common-cover maps. -/
def middleComparison (i j : ι) : (ρ.chart i).sheaf D ≅ (ρ.chart j).sheaf D :=
  D.chartCrossCoverIso ρ.ringMap p ρ.base (ρ.cover i) (ρ.cover j)
    (ρ.cover_square i) (ρ.cover_square j) ρ.faithfullyFlat

/-- Compare the original chart sheaves after pullback to the common affine base. -/
def effectiveComparison (i j : ι) :
    (pullback (Spec.map (ρ.baseMap i))).obj ((C i).sheaf D) ≅
      (pullback (Spec.map (ρ.baseMap j))).obj ((C j).sheaf D) :=
  (C i).comparison (ρ.chart i) D (ρ.refinement i) ≪≫ ρ.middleComparison D i j ≪≫
    ((C j).comparison (ρ.chart j) D (ρ.refinement j)).symm

attribute [local irreducible] middleComparison Chart.comparison
  SchemeGeometricDescent.Data.chartCrossCoverIso

/-- The middle comparisons have the effective affine cross-cover cocycle. -/
theorem middleComparison_cocycle (i j k : ι) :
    (ρ.middleComparison D i j).hom ≫ (ρ.middleComparison D j k).hom =
      (ρ.middleComparison D i k).hom := by
  unfold middleComparison
  exact D.chartCrossCoverIso_cocycle ρ.ringMap p ρ.base (ρ.cover i) (ρ.cover j) (ρ.cover k)
    (ρ.cover_square i) (ρ.cover_square j) (ρ.cover_square k) ρ.faithfullyFlat

private theorem conjugate_cocycle {A : Type*} [Category A]
    {a b c x y z : A} (e : a ≅ x) (f : b ≅ y) (g : c ≅ z)
    (r : x ≅ y) (s : y ≅ z) (t : x ≅ z) (h : r.hom ≫ s.hom = t.hom) :
    (e ≪≫ r ≪≫ f.symm).hom ≫ (f ≪≫ s ≪≫ g.symm).hom =
      (e ≪≫ t ≪≫ g.symm).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc r.hom s.hom, h]

/-- The effective comparisons of the original chart sheaves satisfy the cocycle. -/
theorem effectiveComparison_cocycle (i j k : ι) :
    (ρ.effectiveComparison D i j).hom ≫ (ρ.effectiveComparison D j k).hom =
      (ρ.effectiveComparison D i k).hom :=
  conjugate_cocycle
    ((C i).comparison (ρ.chart i) D (ρ.refinement i))
    ((C j).comparison (ρ.chart j) D (ρ.refinement j))
    ((C k).comparison (ρ.chart k) D (ρ.refinement k))
    (ρ.middleComparison D i j) (ρ.middleComparison D j k) (ρ.middleComparison D i k)
    (ρ.middleComparison_cocycle D i j k)

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinementFamily
