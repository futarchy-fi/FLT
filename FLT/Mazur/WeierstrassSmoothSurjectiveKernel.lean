/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothSquareZeroPowers

/-!
# Smooth-group kernels for arbitrary surjective coefficient maps

The quotient presentation of a surjective algebra map identifies its actual
group-point reduction kernel with the constructed square-zero quotient kernel.
This retains the given coefficient map, as needed for adjacent adic stages.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (W : WeierstrassCurve R) (φ : A →ₐ[R] B)

/-- The original algebra restriction as an actual relative test-scheme morphism. -/
def smoothAlgebraTestMap :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    exact congrArg (fun f : R →+* B ↦ Spec.map (CommRingCat.ofHom f))
      (RingHom.ext φ.commutes))

/-- Smooth-group reduction along the specified algebra homomorphism. -/
def smoothAlgebraReduction :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralSmoothGroup W).X) →*
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      (integralSmoothGroup W).X) where
  toFun p := smoothAlgebraTestMap φ ≫ p
  map_one' := comp_one _
  map_mul' := comp_mul _

/-- The actual surjective reduction has exactly the kernel of its quotient presentation. -/
theorem smoothAlgebraReduction_ker (hφ : Function.Surjective φ) :
    (smoothAlgebraReduction W φ).ker =
      (smoothSquareZeroReduction W (RingHom.ker φ.toRingHom)).ker := by
  let e := φ.toRingHom.quotientKerEquivOfSurjective hφ
  let q := Spec.map (CommRingCat.ofHom e.toRingHom)
  have hq : IsIso q := by
    change IsIso (Spec.map e.toCommRingCatIso.hom)
    infer_instance
  let _ := hq
  have hc : q ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (RingHom.ker φ.toRingHom))) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  ext p
  change (smoothAlgebraTestMap φ ≫ p = 1) ↔
    (squareZeroQuotientTestMap (RingHom.ker φ.toRingHom) ≫ p = 1)
  have hzero : q ≫ (1 : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap R (A ⧸ RingHom.ker φ.toRingHom)))) ⟶ (integralSmoothGroup W).X).left =
      (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
        (integralSmoothGroup W).X).left := by
    change q ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (A ⧸ RingHom.ker φ.toRingHom))) ≫ integralSmoothZero W = _
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    ext r
    exact φ.commutes r
  constructor
  · intro h
    apply Over.OverMorphism.ext
    apply (cancel_epi q).mp
    change q ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ p.left) = _
    rw [← Category.assoc, hc, hzero]
    exact congrArg Over.Hom.left h
  · intro h
    apply Over.OverMorphism.ext
    have he := congrArg (fun a ↦ q ≫ a.left) h
    change q ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ p.left) = _ at he
    rw [← Category.assoc, hc, hzero] at he
    exact he

/-- Unit-index powers are bijective in the actual kernel of any square-zero surjection. -/
theorem smoothAlgebraReduction_kernel_pow_bijective (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.toRingHom ^ 2 = ⊥) (n : ℕ) (hn : IsUnit (n : A)) :
    Function.Bijective (fun z : (smoothAlgebraReduction W φ).ker ↦ z ^ n) := by
  rw [smoothAlgebraReduction_ker W φ hφ]
  exact smoothSquareZeroKernel_pow_bijective W _ hker n hn

end FLT.Mazur.WeierstrassIntegralChart
