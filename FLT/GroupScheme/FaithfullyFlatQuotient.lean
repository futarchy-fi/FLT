/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Faithful flatness after quotienting by an extended ideal

Quotienting both sides of a faithfully flat ring map by an ideal and its
extension is base change, so the induced map remains faithfully flat.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace RingHom

variable {A B : Type} [CommRing A] [CommRing B]

/-- The map on quotients by an ideal and its extension is faithfully flat. -/
theorem FaithfullyFlat.quotientMap (f : A →+* B) (hf : f.FaithfullyFlat)
    (I : Ideal A) (J : Ideal B) (hJ : J = I.map f)
    (hIJ : I ≤ J.comap f) : (Ideal.quotientMap J f hIJ).FaithfullyFlat := by
  subst J
  let originalAlgebra : Algebra A B := f.toAlgebra
  let originalFlat : Module.FaithfullyFlat A B := hf
  let quotientAlgebra : Algebra (A ⧸ I) (B ⧸ I.map f) :=
    Ideal.Quotient.algebraQuotientOfLEComap hIJ
  have h : Module.FaithfullyFlat (A ⧸ I) (B ⧸ I.map f) := by
    apply Module.FaithfullyFlat.of_linearEquiv (A ⧸ I) ((A ⧸ I) ⊗[A] B)
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv
  exact (faithfullyFlat_algebraMap_iff).mpr h

end RingHom
