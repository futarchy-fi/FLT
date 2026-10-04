/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioBasicOpen
public import FLT.Mazur.ProjectiveChartEvaluation

/-!
# Projective chart morphisms from actual section ratios

Every denominator gives a ring map from its standard projective chart, using
the established polynomial equivalence and a coordinate permutation. The
resulting scheme map has the required inverse-image chart opens. Compatibility
between maps with different denominators is a separate gluing obligation.
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
    (t : Fin (n + 1) → Γ(M, ⊤)) (i : Fin (n + 1))
    (U : X.Opens) (hi : U ≤ sectionGeneratorOpen M (t i)) (r : R →+* Γ(X, U))

/-- The actual chart ring map defined by the ratios of global sections. -/
def sectionProjectiveChartRingMap : chartRing R (Fin (n + 1)) i →+* Γ(X, U) :=
  chartEvaluation R Γ(X, U) n (Equiv.swap 0 i) i (by simp) r
    (fun j ↦ sectionRatioOn M (t i) U hi (t j))

/-- Every homogeneous chart coordinate maps to its actual section ratio. -/
lemma sectionProjectiveChartRingMap_coordinate (j : Fin (n + 1)) :
    sectionProjectiveChartRingMap M n t i U hi r (coordinate R (Fin (n + 1)) i j) =
      sectionRatioOn M (t i) U hi (t j) :=
  chartEvaluation_coordinate R Γ(X, U) n (Equiv.swap 0 i) i (by simp) r _
    (sectionRatioOn_self M (t i) U hi) j

/-- The chart ring map respects the given scalar map. -/
lemma sectionProjectiveChartRingMap_scalar (a : R) :
    sectionProjectiveChartRingMap M n t i U hi r (chartScalars R (Fin (n + 1)) i a) =
      r a :=
  chartEvaluation_scalar R Γ(X, U) n (Equiv.swap 0 i) i (by simp) r _ a

/-- The actual local morphism to projective space supplied by one denominator. -/
def sectionProjectiveChartMorphism : U.toScheme ⟶ space R (Fin (n + 1)) :=
  U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (U.topIso.inv.hom.comp (sectionProjectiveChartRingMap M n t i U hi r))) ≫
      chartMap R (Fin (n + 1)) i

/-- Pulling back a target chart gives the basic open of its section ratio. -/
lemma sectionProjectiveChartMorphism_preimage (j : Fin (n + 1)) :
    sectionProjectiveChartMorphism M n t i U hi r ⁻¹ᵁ chart R (Fin (n + 1)) j =
      U.toScheme.basicOpen (U.topIso.inv (sectionRatioOn M (t i) U hi (t j))) := by
  rw [sectionProjectiveChartMorphism, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage, chartMap_preimage_chart, SpecMap_preimage_basicOpen,
    Scheme.toSpecΓ_preimage_basicOpen]
  congr 1
  exact congrArg U.topIso.inv (sectionProjectiveChartRingMap_coordinate M n t i U hi r j)

/-- The inverse-image chart open, viewed in the original scheme, is the generator intersection. -/
lemma sectionProjectiveChartMorphism_preimage_image (j : Fin (n + 1)) :
    U.ι ''ᵁ (sectionProjectiveChartMorphism M n t i U hi r ⁻¹ᵁ
      chart R (Fin (n + 1)) j) = U ⊓ sectionGeneratorOpen M (t j) := by
  rw [sectionProjectiveChartMorphism_preimage, Scheme.Opens.ι_image_basicOpen_topIso_inv,
    sectionRatioOn_basicOpen]

end FLT.Mazur.FCurve
