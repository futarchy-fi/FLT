/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothSurjectiveKernel

/-!
# Naturality of the original smooth infinitesimal points

An algebra map carrying one square-zero ideal into another carries the actual
smooth-group point to the point with the mapped X coordinate. The proof compares
the original cubic chart and cancels its inclusion in the smooth curve.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  (W : WeierstrassCurve R) (φ : A →ₐ[R] B)

/-- Restriction of actual smooth-group points respects composition of algebra maps. -/
theorem smoothAlgebraReduction_comp (ψ : B →ₐ[R] C)
    (p : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralSmoothGroup W).X) :
    smoothAlgebraReduction W (ψ.comp φ) p =
      smoothAlgebraReduction W ψ (smoothAlgebraReduction W φ p) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (ψ.comp φ).toRingHom) ≫ p.left =
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ p.left
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

variable (I : Ideal A) (J : Ideal B) (hI : I ^ 2 = ⊥) (hJ : J ^ 2 = ⊥)
  (hφ : ∀ x ∈ I, φ x ∈ J)

/-- The original infinitesimal chart maps commute with ideal-preserving algebra maps. -/
theorem infinitesimalChartPoint_natural (x : I) :
    φ.comp (infinitesimalChartPoint W I hI x).val =
      (infinitesimalChartPoint W J hJ ⟨φ x, hφ x x.property⟩).val := by
  apply hom_ext
  intro i
  fin_cases i <;> simp [AlgHom.comp_apply, infinitesimalChartPoint, evaluation_coord]

/-- Naturality holds in the full smooth group, retaining the original chart parameter. -/
theorem smoothInfinitesimalPoint_natural (x : I) :
    smoothAlgebraReduction W φ (smoothInfinitesimalPoint W I hI x) =
      smoothInfinitesimalPoint W J hJ ⟨φ x, hφ x x.property⟩ := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  change (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ _) ≫ _ = _
  rw [Category.assoc, smoothInfinitesimalPoint_inclusion,
    smoothInfinitesimalPoint_inclusion, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (φ.comp (infinitesimalChartPoint W I hI x).val).toRingHom) ≫ _ = _
  rw [infinitesimalChartPoint_natural W φ I J hI hJ hφ]

end FLT.Mazur.WeierstrassIntegralChart
