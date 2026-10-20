/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteOriginalScaleOpen
public import FLT.Mazur.WeierstrassFiveRegularSectionDescent

/-!
# Finite-model output uniqueness over flat source schemes

The original scale remains regular on every affine chart of a flat
source. The proved regular-scale uniqueness therefore compares arbitrary
finite-model outputs contracting to the same affine cubic morphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (k : ℕ) (hk : k ≤ n)

/-- Flatness over the coefficient ring suffices for uniqueness of affine-output lifts. -/
theorem finiteGlobalContraction_ext_of_flat_source {X : Scheme.{u}}
    (h : X ⟶ Spec (.of (Coordinate W 2))) [Flat (h ≫ chartStructure W 2)]
    (f g : X ⟶ finiteGlobalModel hπ data k hk)
    (hf : f ≫ finiteGlobalContraction hπ data k hk = h ≫ integralCurveChart W 2)
    (hg : g ≫ finiteGlobalContraction hπ data k hk = h ≫ integralCurveChart W 2) :
    f = g := by
  apply X.affineCover.hom_ext
  intro i
  let φ := affineChartRingHom (X.affineCover.f i ≫ h)
  have hφ : Spec.map (CommRingCat.ofHom φ) = X.affineCover.f i ≫ h :=
    affineChartRingHom_spec _
  have hb : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap R (Coordinate W 2)))) =
      X.affineCover.f i ≫ h ≫ chartStructure W 2 := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hφ, Category.assoc]
    rfl
  have hflat : (φ.comp (algebraMap R (Coordinate W 2))).Flat := by
    have hm : Flat (Spec.map
        (CommRingCat.ofHom (φ.comp (algebraMap R (Coordinate W 2))))) := by
      rw [hb]
      infer_instance
    exact Flat.SpecMap_iff.mp hm
  apply finiteGlobalContraction_ext_of_regular_scale hπ data k hk φ
    (flatRingHom_isRegular _ hflat (IsRegular.of_ne_zero hπ))
  · rw [Category.assoc, hf, hφ, Category.assoc]
  · rw [Category.assoc, hg, hφ, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
