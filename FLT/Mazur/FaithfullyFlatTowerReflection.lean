/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Reflection of flatness through a faithfully flat extension of the target

If a faithfully flat extension of an algebra is flat over the original base,
the original algebra is flat over that base. Tensor cancellation identifies
the tested maps, and faithful flatness reflects their injectivity.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FaithfullyFlatTowerReflection
variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Flatness over the original base descends through a faithfully flat algebra extension. -/
theorem flat_of_tower [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ u hu
  let v := AlgebraTensorModule.lTensor S S u
  change Function.Injective v
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T v).mp
  let eN := AlgebraTensorModule.cancelBaseChange R S S T N
  let eP := AlgebraTensorModule.cancelBaseChange R S S T P
  have h : (eP.toLinearMap.comp (LinearMap.lTensor T v)) =
      (AlgebraTensorModule.lTensor S T u).comp eN.toLinearMap := by
    ext
    simp [eN, eP, v]
  have hi : Function.Injective ((AlgebraTensorModule.lTensor S T u).comp eN.toLinearMap) :=
    (Module.Flat.lTensor_preserves_injective_linearMap u hu).comp eN.injective
  rw [← h] at hi
  intro x y hxy
  exact hi (congrArg eP hxy)

/-- Ring-map form of reflection, suitable for the actual maps on scheme stalks. -/
theorem ringHom_flat_of_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) (hb : b.FaithfullyFlat) (hab : (b.comp a).Flat) :
    a.Flat := by
  algebraize [a, b, b.comp a]
  exact flat_of_tower A B C

end FLT.Mazur.FaithfullyFlatTowerReflection
