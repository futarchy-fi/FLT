/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicExtensionHomotopy

/-!
# First homology of homotopy-equivalent completed conormal complexes

Actual extension morphisms in both directions induce inverse maps on
completed conormal kernels. No invertibility of the individual chain maps,
Noetherianity, or comparison of differential cokernels is assumed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicExtensionKernelComparison

open Algebra.Extension AdicExtensionHomotopy

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) {P Q T : Algebra.Extension R A}

/-- Restrict the actual completed degree-one map to the kernel of its differential. -/
def map (f : P.Hom Q) :
    LinearMap.ker (AdicCompletion.map I P.cotangentComplex) →ₗ[AdicCompletion I A]
      LinearMap.ker (AdicCompletion.map I Q.cotangentComplex) :=
  (conormalMap I f).restrict fun x hx ↦ by
    change AdicCompletion.map I Q.cotangentComplex (conormalMap I f x) = 0
    rw [← LinearMap.comp_apply, ← chainMap, LinearMap.comp_apply]
    rw [LinearMap.mem_ker.mp hx, map_zero]

/-- The kernel map retains the actual completed conormal map. -/
@[simp] theorem map_val (f : P.Hom Q)
    (x : LinearMap.ker (AdicCompletion.map I P.cotangentComplex)) :
    (map I f x).val = conormalMap I f x.val := rfl

/-- The explicit completed homotopy makes the map on kernels independent of the lift. -/
theorem map_eq (f g : P.Hom Q) : map I f = map I g := by
  ext x : 1
  apply Subtype.ext
  change conormalMap I f x.val = conormalMap I g x.val
  rw [← sub_eq_zero, ← LinearMap.sub_apply, conormalMap_sub, LinearMap.comp_apply]
  rw [LinearMap.mem_ker.mp x.property, map_zero]

/-- Identity extension maps act identically on completed first homology. -/
@[simp] theorem map_id : map I (Hom.id P) = LinearMap.id := by
  ext x : 1
  apply Subtype.ext
  exact LinearMap.congr_fun (conormalMap_id I) x.val

/-- Composition of extension lifts agrees with composition on completed first homology. -/
theorem map_comp (f : P.Hom Q) (g : Q.Hom T) :
    map I (g.comp f) = (map I g).comp (map I f) := by
  ext x : 1
  apply Subtype.ext
  exact LinearMap.congr_fun (conormalMap_comp I f g) x.val

/-- Bidirectional extension lifts give an equivalence of completed conormal kernels. -/
def equiv (f : P.Hom Q) (g : Q.Hom P) :
    LinearMap.ker (AdicCompletion.map I P.cotangentComplex) ≃ₗ[AdicCompletion I A]
      LinearMap.ker (AdicCompletion.map I Q.cotangentComplex) :=
  { map I f with
    invFun := map I g
    left_inv := fun x ↦ by
      change ((map I g).comp (map I f)) x = x
      rw [← map_comp, map_eq I (g.comp f) (Hom.id P), map_id, LinearMap.id_apply]
    right_inv := fun x ↦ by
      change ((map I f).comp (map I g)) x = x
      rw [← map_comp, map_eq I (f.comp g) (Hom.id Q), map_id, LinearMap.id_apply] }

/-- The equivalence uses the forward lift on conormal representatives. -/
@[simp] theorem equiv_val (f : P.Hom Q) (g : Q.Hom P)
    (x : LinearMap.ker (AdicCompletion.map I P.cotangentComplex)) :
    (equiv I f g x).val = conormalMap I f x.val := rfl

/-- The inverse equivalence uses the reverse lift on conormal representatives. -/
@[simp] theorem equiv_symm_val (f : P.Hom Q) (g : Q.Hom P)
    (x : LinearMap.ker (AdicCompletion.map I Q.cotangentComplex)) :
    ((equiv I f g).symm x).val = conormalMap I g x.val := rfl

end FLT.Mazur.AdicExtensionKernelComparison
