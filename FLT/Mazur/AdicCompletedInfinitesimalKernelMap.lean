/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletedInfinitesimalChainMap

/-!
# Constructed maps on kernels of completed original complexes

The proved original chain map restricts to the first-homology kernels.
This is a map, with the genuine formal scalar action; inverse identities
still require the explicit difference homotopies.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletedInfinitesimalKernelMap

universe u

variable {R A B ι : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Finite ι] (P : Algebra.Generators R A ι)
  (Q : Algebra.Extension.{u} R B)
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  (I : Ideal A) (J : Ideal B) [I.IsMaximal] [J.IsMaximal]
  (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)

/-- The constructed original chain map restricts to a semilinear map of its degree-one kernels. -/
def map : LinearMap.ker (AdicCompletion.map I P.toExtension.cotangentComplex)
    →ₛₗ[e.toRingHom] LinearMap.ker (AdicCompletion.map J Q.cotangentComplex) where
  toFun x := ⟨AdicCompletedInfinitesimalHom.conormalMap P Q I J e x.val, by
    rw [LinearMap.mem_ker, ← AdicCompletedInfinitesimalChainMap.chainMap]
    rw [show AdicCompletion.map I P.toExtension.cotangentComplex x.val = 0 from x.property,
      map_zero]⟩
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' a x := Subtype.ext
    (AdicCompletedInfinitesimalHom.conormalMap_smul P Q I J e a x.val)

/-- On first-homology kernels the map is the existing completed original conormal map. -/
@[simp] theorem map_val
    (x : LinearMap.ker (AdicCompletion.map I P.toExtension.cotangentComplex)) :
    (map P Q I J e x).val = AdicCompletedInfinitesimalHom.conormalMap P Q I J e x.val := rfl

end FLT.Mazur.AdicCompletedInfinitesimalKernelMap
