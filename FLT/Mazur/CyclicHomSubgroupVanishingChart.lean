/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomDivisorProduct
public import FLT.Mazur.FiniteFlatIdealVanishingChart

/-!
# Closed coefficient charts for the actual cyclic subgroup equation

Each affine parameter open has an actual closed scheme representing vanishing
of the multiplication ideal in the finite product algebra. In particular this
applies to the universal parameter. Compatibility and gluing of these charts
are separate from their construction and affine-test universal property.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (U : T.affineOpens)
set_option quotPrecheck false in
local notation "p" => (cyclicHomDivisorProduct n f).hom
set_option quotPrecheck false in
local notation "R" => Γ(T, U.1)
set_option quotPrecheck false in
local notation "B" => Γ((cyclicHomDivisorProduct n f).left, p ⁻¹ᵁ U.1)
/-- The actual product structure map supplies the coefficient scalar action. -/
local instance cyclicHomProductSectionAlgebra : Algebra R B :=
  ((cyclicHomDivisorProduct n f).hom.app U.1).hom.toAlgebra

/-- An actual closed coefficient chart for the source multiplication ideal. -/
def cyclicHomSubgroupChart : Scheme :=
  FiniteFlatIdealVanishing.chart p (cyclicHomMultiplicationIdeal n f) U

/-- The chart's original closed immersion into the affine coefficient base. -/
def cyclicHomSubgroupChartInclusion : cyclicHomSubgroupChart n f U ⟶ Spec (.of R) :=
  FiniteFlatIdealVanishing.chartInclusion p (cyclicHomMultiplicationIdeal n f) U

instance cyclicHomSubgroupChartInclusion_closed :
    IsClosedImmersion (cyclicHomSubgroupChartInclusion n f U) :=
  FiniteFlatIdealVanishing.chartInclusion_closed _ _ _

/-- Tests lift precisely when they kill the actual extended multiplication ideal. -/
theorem cyclicHomSubgroupChart_factorization_iff (A : Type) [CommRing A] [Algebra R A] :
    (∃ k : Spec (.of A) ⟶ cyclicHomSubgroupChart n f U,
      k ≫ cyclicHomSubgroupChartInclusion n f U =
        Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔
      (FiniteFlatIdealVanishing.preimageIdeal p (cyclicHomMultiplicationIdeal n f) U).map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom = ⊥ :=
  FiniteFlatIdealVanishing.chart_factorization_iff p (cyclicHomMultiplicationIdeal n f) U A

/-- These closed charts exist on every affine open of the actual universal parameter scheme. -/
def cyclicHomUniversalSubgroupChart (V : (cyclicHomAuxiliaryScheme n).left.affineOpens) : Scheme :=
  cyclicHomSubgroupChart n (𝟙 _) V

end FLT.Mazur.UniversalWeierstrass
