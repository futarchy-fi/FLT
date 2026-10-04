/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Reduction of a quotient by lifted equations

The kernel of the induced quotient map consists exactly of the extended
coefficient kernel. No flatness of either quotient is required.
-/

@[expose] public noncomputable section
namespace Ideal
variable {P Q : Type*} [CommRing P] [CommRing Q]

set_option backward.isDefEq.respectTransparency false in
/-- Quotienting by relations commutes with a surjection, with the expected kernel. -/
theorem ker_quotientMap_of_surjective (f : P →+* Q) (hf : Function.Surjective f)
    (L : Ideal P) :
    RingHom.ker (quotientMap (L.map f) f le_comap_map) =
      (RingHom.ker f).map (Quotient.mk L) := by
  rw [quotientMap, ker_quotient_lift, ← RingHom.comap_ker, mk_ker,
    comap_map_of_surjective _ hf, ← RingHom.ker_eq_comap_bot,
    map_sup, map_quotient_self, bot_sup_eq]

/-- The reduction of the lifted quotient is the original quotient, as an actual isomorphism. -/
def reductionQuotientEquiv (f : P →+* Q) (hf : Function.Surjective f) (L : Ideal P) :
    ((P ⧸ L) ⧸ (RingHom.ker f).map (Quotient.mk L)) ≃+* (Q ⧸ L.map f) :=
  (quotientEquiv _ _ (RingEquiv.refl _) (by
    change _ = Ideal.map (RingHom.id _) _
    rw [Ideal.map_id, ker_quotientMap_of_surjective f hf L])).trans
    (RingHom.quotientKerEquivOfSurjective
      (quotientMap_surjective (H := le_comap_map) hf))

/-- The reduction isomorphism retains the image of every polynomial representative. -/
@[simp]
theorem reductionQuotientEquiv_mk (f : P →+* Q) (hf : Function.Surjective f)
    (L : Ideal P) (x : P) :
    reductionQuotientEquiv f hf L
      (Quotient.mk _ (Quotient.mk L x)) = Quotient.mk (L.map f) (f x) := by
  rfl

end Ideal
