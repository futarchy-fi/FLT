/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.Maps

/-! # Kernels in a surjective quotient square -/

@[expose] public section
namespace RingHom
variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

/-- In a commuting quotient square, pulling back the quotient ideal makes the
kernel of the bottom map the image of the top kernel. -/
theorem map_ker_of_surjective_square (f : A →+* B) (q : A →+* C)
    (r : B →+* D) (g : C →+* D) (hf : Function.Surjective f)
    (hq : Function.Surjective q) (hsquare : g.comp q = r.comp f)
    (hker : (ker q).map f = ker r) : (ker f).map q = ker g := by
  apply Ideal.comap_injective_of_surjective q hq
  rw [Ideal.comap_map_of_surjective q hq, comap_ker, hsquare,
    ← comap_ker, ← hker, Ideal.comap_map_of_surjective f hf]
  exact sup_comm _ _
end RingHom
