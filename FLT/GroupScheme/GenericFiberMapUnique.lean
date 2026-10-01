/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Uniqueness of maps from their generic fibers

A flat algebra over a domain embeds in its scalar extension to the fraction
field. Consequently two algebra maps into it agree if their generic fibers
agree. No Hopf algebra structure or flatness of the source is needed.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra

variable {O K A B : Type*} [CommRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [CommRing A] [Algebra O A]
  [CommRing B] [Algebra O B] [Module.Flat O B]

/-- A flat algebra embeds in its generic fiber over a domain. -/
theorem genericFiber_includeRight_injective :
    Function.Injective (TensorProduct.includeRight : B →ₐ[O] K ⊗[O] B) :=
  TensorProduct.includeRight_injective (IsFractionRing.injective O K)

/-- An algebra map into a flat model is determined by its generic fiber. -/
theorem modelMap_unique (f g : A →ₐ[O] B)
    (h : (TensorProduct.includeRight : B →ₐ[O] K ⊗[O] B).comp f =
      (TensorProduct.includeRight : B →ₐ[O] K ⊗[O] B).comp g) : f = g := by
  ext a
  exact genericFiber_includeRight_injective (K := K) (DFunLike.congr_fun h a)

end Algebra
