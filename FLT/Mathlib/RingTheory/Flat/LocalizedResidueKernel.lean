/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.LocalizedResidueQuotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # The full presentation kernel in the localized residue-fibre square -/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace Ideal.Fiber

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] (p : Ideal R) [p.IsPrime]
  (q : Ideal (p.Fiber S)) [q.IsPrime]

/-- Extending an original ideal into the localized fibre agrees with first
localizing the original ideal and then reducing by the extended base prime. -/
theorem map_ideal_localizedQuotientEquiv (I : Ideal S) :
    ((I.map (includeRight : S →ₐ[R] p.Fiber S).toRingHom).map
      (algebraMap (p.Fiber S) (Localization.AtPrime q))).map
        (localizedQuotientEquiv p q).toRingHom =
    (I.map (algebraMap S (Localization.AtPrime (q.comap includeRight)))).map
      (Ideal.Quotient.mk (p.map (algebraMap R
        (Localization.AtPrime (q.comap includeRight))))) := by
  simp only [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro s
  exact localizedQuotientEquiv_algebraMap_one_tmul p q s

/-- Tensor right exactness and the coordinate comparison identify the entire
localized fibre kernel with the reduction of the original localized kernel. -/
theorem map_kernel_localizedQuotientEquiv (f : S →ₐ[R] A)
    (hf : Function.Surjective f) :
    ((RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R p.ResidueField) f)).map
      (algebraMap (p.Fiber S) (Localization.AtPrime q))).map
        (localizedQuotientEquiv p q).toRingHom =
    ((RingHom.ker f).map
      (algebraMap S (Localization.AtPrime (q.comap includeRight)))).map
        (Ideal.Quotient.mk (p.map (algebraMap R
          (Localization.AtPrime (q.comap includeRight))))) := by
  rw [Algebra.TensorProduct.lTensor_ker f hf]
  exact map_ideal_localizedQuotientEquiv p q (RingHom.ker f)

/-- Kernel transport with an explicitly identified original prime. -/
theorem map_kernel_localizedQuotientEquivOfEq (f : S →ₐ[R] A)
    (hf : Function.Surjective f) (P : Ideal S) [P.IsPrime]
    (hP : q.comap includeRight = P) :
    ((RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R p.ResidueField) f)).map
      (algebraMap (p.Fiber S) (Localization.AtPrime q))).map
        (localizedQuotientEquivOfEq p q P hP).toRingHom =
    ((RingHom.ker f).map (algebraMap S (Localization.AtPrime P))).map
      (Ideal.Quotient.mk (p.map (algebraMap R (Localization.AtPrime P)))) := by
  subst P
  exact map_kernel_localizedQuotientEquiv p q f hf

end Ideal.Fiber
