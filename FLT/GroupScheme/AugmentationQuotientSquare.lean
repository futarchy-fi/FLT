/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsor

/-! # Augmentation ideals in a surjective bialgebra square -/

@[expose] public section
namespace HopfAlgebra
variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D] [HopfAlgebra R A] [HopfAlgebra R B]
  [HopfAlgebra R C] [HopfAlgebra R D]

/-- The augmentation-kernel ideal commutes with a quotient square when the
map on the target group's coordinate algebra is surjective. -/
theorem augmentationIdeal_map_of_quotient_square (f : B →ₐc[R] A)
    (q : A →ₐc[R] C) (r : B →ₐc[R] D) (g : D →ₐc[R] C)
    (hr : Function.Surjective r) (hsquare : q.comp f = g.comp r) :
    (augmentationIdeal f).map q.toAlgHom.toRingHom = augmentationIdeal g := by
  have hc : (Bialgebra.counitAlgHom R D).toRingHom.comp r.toAlgHom.toRingHom =
      (Bialgebra.counitAlgHom R B).toRingHom := by
    ext b
    exact CoalgHomClass.counit_comp_apply r b
  have hk : (RingHom.ker (Bialgebra.counitAlgHom R B).toRingHom).map
      r.toAlgHom.toRingHom = RingHom.ker (Bialgebra.counitAlgHom R D).toRingHom := by
    rw [← hc, ← RingHom.comap_ker]
    exact Ideal.map_comap_of_surjective _ hr _
  have hs : q.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom =
      g.toAlgHom.toRingHom.comp r.toAlgHom.toRingHom :=
    congrArg (fun k : B →ₐc[R] C ↦ k.toAlgHom.toRingHom) hsquare
  unfold augmentationIdeal
  rw [Ideal.map_map, hs, ← Ideal.map_map, hk]
end HopfAlgebra
