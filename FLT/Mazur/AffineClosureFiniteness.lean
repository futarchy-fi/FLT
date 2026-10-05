/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AffineGenericClosure
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finiteness and rank of an affine generic closure

Integral images of a finite set of chart generators make the closure finite.
Over a PID its flat coordinate module is free, with rank determined by the
prescribed generic fibre. Integrality of the generators is a separate geometric
obligation; generic finite dimension alone does not suffice.
-/

@[expose] public section

open scoped TensorProduct

namespace FLT.Mazur.AffineGenericClosure

variable {R K A B : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

/-- Integral images of finitely many chart generators make the closure finite. -/
theorem finite_of_integral_generators (f : A →ₐ[R] B) (s : Set A) (hs : s.Finite)
    (hgen : Algebra.adjoin R s = ⊤) (hint : ∀ a ∈ s, IsIntegral R (f a)) :
    Module.Finite R (Coordinate f) := by
  have hrange : Algebra.adjoin R (f '' s) = f.range := by
    rw [Algebra.adjoin_image, hgen, Algebra.map_top]
  have hi : ∀ b ∈ f '' s, IsIntegral R b := by
    rintro b ⟨a, ha, rfl⟩
    exact hint a ha
  have hfinite := Algebra.finite_adjoin_of_finite_of_isIntegral (hs.image f) hi
  rw [hrange] at hfinite
  let _ := hfinite
  exact Module.Finite.equiv (imageEquiv f).symm.toLinearEquiv

variable (K) [Field K] [Algebra R K] [IsFractionRing R K]
  [Algebra K B] [IsScalarTower R K B]

/-- Once finite, the closure over a PID has the rank of its generic fibre. -/
theorem finrank_eq [IsDomain R] [IsPrincipalIdealRing R] (f : A →ₐ[R] B)
    [Module.Finite R (Coordinate f)]
    (hf : Function.Surjective (AlgHom.liftEquiv R K A B f)) :
    Module.finrank R (Coordinate f) = Module.finrank K B := by
  let _ := isTorsionFree K f
  let _ : Module.Free R (Coordinate f) := inferInstance
  let e : K ⊗[R] Coordinate f ≃ₐ[K] B :=
    AlgEquiv.ofBijective (genericMap K f)
      ⟨genericMap_injective K f, genericMap_surjective K f hf⟩
  rw [← Module.finrank_baseChange (R := K) (S := R) (M' := Coordinate f)]
  exact e.toLinearEquiv.finrank_eq

end FLT.Mazur.AffineGenericClosure
