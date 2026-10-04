/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionProjectiveChart
public import FLT.Mazur.ProjectiveChartMapCompatibility

/-!
# Actual section-chart overlap identities

Restriction and change of denominator commute with the actual scheme morphisms,
using scalar and coordinate extensionality of the homogeneous chart rings.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
attribute [local instance] MvPolynomial.gradedAlgebra
open ProjectiveSpace
variable {X : Scheme.{u}} (M : X.Modules) {R : Type u} [CommRing R] (n : ℕ)
    (t : Fin (n + 1) → Γ(M, ⊤))

/-- On one common open, changing the generating denominator leaves the scheme map unchanged. -/
lemma sectionProjectiveChartMorphism_change (i j : Fin (n + 1)) (U : X.Opens)
    (hi : U ≤ sectionGeneratorOpen M (t i)) (hj : U ≤ sectionGeneratorOpen M (t j))
    (r : R →+* Γ(X, U)) :
    sectionProjectiveChartMorphism M n t i U hi r =
      sectionProjectiveChartMorphism M n t j U hj r := by
  apply congrArg (fun f ↦ U.toScheme.toSpecΓ ≫ f)
  apply chartMaps_eq_of_coordinates
  · intro a
    change U.topIso.inv (sectionProjectiveChartRingMap M n t i U hi r
      (chartScalars R (Fin (n + 1)) i a)) =
        U.topIso.inv (sectionProjectiveChartRingMap M n t j U hj r
          (chartScalars R (Fin (n + 1)) j a))
    rw [sectionProjectiveChartRingMap_scalar, sectionProjectiveChartRingMap_scalar]
  · intro k
    change U.topIso.inv (sectionProjectiveChartRingMap M n t i U hi r
      (coordinate R (Fin (n + 1)) i k)) =
        U.topIso.inv (sectionProjectiveChartRingMap M n t j U hj r
          (coordinate R (Fin (n + 1)) j k)) *
        U.topIso.inv (sectionProjectiveChartRingMap M n t i U hi r
          (coordinate R (Fin (n + 1)) i j))
    rw [sectionProjectiveChartRingMap_coordinate, sectionProjectiveChartRingMap_coordinate,
      sectionProjectiveChartRingMap_coordinate, ← map_mul, mul_comm, sectionRatioOn_change]
  · change IsUnit (U.topIso.inv (sectionProjectiveChartRingMap M n t i U hi r
      (coordinate R (Fin (n + 1)) i j)))
    rw [sectionProjectiveChartRingMap_coordinate]
    exact (sectionRatioOn_isUnit M (t i) (t j) U hi hj).map U.topIso.inv.hom

/-- The chart-ring maps commute with ambient structure-sheaf restriction. -/
lemma sectionProjectiveChartRingMap_restrict (i : Fin (n + 1)) (U V : X.Opens)
    (hi : U ≤ sectionGeneratorOpen M (t i)) (hVU : V ≤ U) (r : R →+* Γ(X, U)) :
    (X.presheaf.map (homOfLE hVU).op).hom.comp
        (sectionProjectiveChartRingMap M n t i U hi r) =
      sectionProjectiveChartRingMap M n t i V (hVU.trans hi)
        ((X.presheaf.map (homOfLE hVU).op).hom.comp r) := by
  apply chartRing_hom_ext R (Fin (n + 1)) i
  · intro a
    simp only [RingHom.comp_apply, sectionProjectiveChartRingMap_scalar]
  · intro j
    simp only [RingHom.comp_apply, sectionProjectiveChartRingMap_coordinate]
    exact sectionRatioOn_restrict M (t i) U V hi hVU (t j)

/-- Top-open coordinate transport respects nested open inclusions. -/
lemma homOfLE_topIso_inv (U V : X.Opens) (hVU : V ≤ U) (a : Γ(X, U)) :
    (X.homOfLE hVU).appTop (U.topIso.inv a) =
      V.topIso.inv (X.presheaf.map (homOfLE hVU).op a) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The actual projective chart morphisms commute with restriction to smaller source opens. -/
lemma sectionProjectiveChartMorphism_restrict (i : Fin (n + 1)) (U V : X.Opens)
    (hi : U ≤ sectionGeneratorOpen M (t i)) (hVU : V ≤ U) (r : R →+* Γ(X, U)) :
    X.homOfLE hVU ≫ sectionProjectiveChartMorphism M n t i U hi r =
      sectionProjectiveChartMorphism M n t i V (hVU.trans hi)
        ((X.presheaf.map (homOfLE hVU).op).hom.comp r) := by
  rw [sectionProjectiveChartMorphism, ← Category.assoc, Scheme.toSpecΓ_naturality]
  simp only [sectionProjectiveChartMorphism, Category.assoc]
  rw [← Spec.map_comp_assoc]
  congr 2
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change (X.homOfLE hVU).appTop
      (U.topIso.inv (sectionProjectiveChartRingMap M n t i U hi r z)) = _
  rw [homOfLE_topIso_inv]
  exact congrArg V.topIso.inv
    (DFunLike.congr_fun (sectionProjectiveChartRingMap_restrict M n t i U V hi hVU r) z)

end FLT.Mazur.FCurve
