/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSquareZeroFormalConormal
public import FLT.Mazur.AdicSquareZeroComplexComparison
public import FLT.Mazur.AdicFormalCotangentSpaceMap

/-!
# Genuine chain maps between completed original square-zero complexes

The formal conormal map and the original degree-zero map commute with the
completed ORIGINAL conormal differentials. The proof retains the images of
original relations and extends by completed scalar linearity.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicSquareZeroFormalChainMap

open AdicExtensionProjection AdicFormalPresentationHom Algebra.Extension

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (I : Ideal A) (J : Ideal B)
  (e : AdicCompletion I A →ₐ[R] AdicCompletion J B)
  (f : AdicCompletion (ideal P I) P.Ring →ₐ[R] AdicCompletion (ideal Q J) Q.Ring)
  (hf : ∀ x, projection Q J (f x) = e (projection P I x))
  [IsNoetherianRing A] [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  [Module.Finite A P.CotangentSpace] (hP : P.ker ^ 2 = ⊥) (hQ : Q.ker ^ 2 = ⊥)

/-- The original relation representative satisfies the genuine completed chain-map identity. -/
theorem chainMap_of_mk (x : P.ker) :
    AdicFormalCotangentSpaceMap.map P Q I J e f hf
      (AdicCompletion.map I P.cotangentComplex
        (AdicCompletion.of I P.Cotangent (Cotangent.mk x))) =
      AdicCompletion.map J Q.cotangentComplex
        (AdicSquareZeroFormalConormal.map P Q I J e f hf hP hQ
          (AdicCompletion.of I P.Cotangent (Cotangent.mk x))) := by
  rw [AdicCompletion.map_of, cotangentComplex_mk,
    AdicFormalCotangentSpaceMap.map_of_tmul, AdicSquareZeroFormalConormal.map_of_mk]
  change e 1 • AdicPresentationDerivation.derivation Q J
    (f (AdicCompletion.of (ideal P I) P.Ring x.val)) = _
  rw [map_one, one_smul, ← AdicSquareZeroComplexComparison.derivation_kernel]
  congr 1

/-- Formal square-zero lifts induce chain maps on the completed ORIGINAL complexes. -/
theorem chainMap (x : AdicCompletion I P.Cotangent) :
    AdicFormalCotangentSpaceMap.map P Q I J e f hf
      (AdicCompletion.map I P.cotangentComplex x) =
      AdicCompletion.map J Q.cotangentComplex
        (AdicSquareZeroFormalConormal.map P Q I J e f hf hP hQ x) := by
  let _ := Cotangent.finite P.ker.fg_of_isNoetherianRing
  obtain ⟨x, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I P.Cotangent x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro a x
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul, LinearMap.map_smulₛₗ,
      LinearMap.map_smulₛₗ, map_smul]
    congr 1
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    exact chainMap_of_mk P Q I J e f hf hP hQ x
  · intro x y hx hy
    simp only [map_add, hx, hy]

end FLT.Mazur.AdicSquareZeroFormalChainMap
