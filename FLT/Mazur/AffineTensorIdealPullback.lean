/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealSheafComparison
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual ideal pullback in tensor coordinates

The ideal on an affine fiber product is the scalar-extended ideal, with its
full scheme structure. Vanishing is preserved by the tensor comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open Scheme.IdealSheafData
namespace FLT.Mazur.AffineTensorIdealPullback
open BaseAdicThickening
set_option backward.isDefEq.respectTransparency false
variable (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (J : Ideal B)

/-- A coordinate ideal vanishes exactly when its actual affine ideal sheaf vanishes. -/
theorem baseIdeal_eq_bot_iff : baseIdeal (.of B) J = ⊥ ↔ J = ⊥ := by
  constructor
  · intro h
    have ht := congrArg (fun I : (Spec (.of B)).IdealSheafData ↦
      I.ideal ⟨⊤, isAffineOpen_top _⟩) h
    rw [baseIdeal_top, ideal_bot, Pi.bot_apply] at ht
    exact (Ideal.map_eq_bot_iff_of_injective
      (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv.injective).mp ht
  · rintro rfl
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp

/-- The actual second-projection pullback ideal in multiplicative tensor coordinates. -/
theorem pullbackIdeal_tensor :
    ((baseIdeal (.of B) J).comap
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B))))).comap
          (pullbackSpecIso R A B).inv =
      baseIdeal (.of (A ⊗[R] B))
        (J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) := by
  rw [← comap_comp, pullbackSpecIso_inv_snd]
  exact baseIdeal_comap_specMap _ _

/-- Zero of the geometric pullback is exactly zero of the full extended ideal. -/
theorem pullbackIdeal_eq_bot_iff :
    (baseIdeal (.of B) J).comap
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))) = ⊥ ↔
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom = ⊥ := by
  rw [← baseIdeal_eq_bot_iff (A ⊗[R] B), ← pullbackIdeal_tensor R A B J]
  constructor
  · intro h
    rw [h, comap_bot]
  · intro h
    have he := congrArg (fun I ↦ I.comap (pullbackSpecIso R A B).hom) h
    simpa only [← comap_comp, Iso.hom_inv_id_assoc, Iso.hom_inv_id, comap_id, comap_bot] using he

end FLT.Mazur.AffineTensorIdealPullback
