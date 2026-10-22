/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorKernelFinite

/-!
# Ideal-tensor comparisons across a square of ring maps

Both the base ring and its algebra may change. The comparison is semilinear
over the algebra transition and commutes with the actual multiplication map.
No flatness or injectivity of either transition is required.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorKernel
variable {R S R' S' : Type*} [CommRing R] [CommRing S]
  [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R' S']
  (r : R →+* R') (s : S →+* S')
  (hs : s.comp (algebraMap R S) = (algebraMap R' S').comp r)

/-- The algebra transition as a semilinear map over the base transition. -/
def algebraTransition : S →ₛₗ[r] S' where
  toFun := s
  map_add' := s.map_add
  map_smul' a x := by
    simp only [Algebra.smul_def, map_mul]
    exact congrArg (fun b ↦ b * s x) (RingHom.congr_fun hs a)

/-- The base transition restricted to an ideal and its actual extended ideal. -/
def idealTransition (I : Ideal R) : I →ₛₗ[r] I.map r where
  toFun x := ⟨r x, Ideal.mem_map_of_mem r x.property⟩
  map_add' x y := Subtype.ext (r.map_add x y)
  map_smul' a x := Subtype.ext (r.map_mul a x)

/-- The comparison retains the larger algebra's semilinear structure. -/
def transition (I : Ideal R) : S ⊗[R] I →ₛₗ[s] S' ⊗[R'] I.map r where
  toFun := TensorProduct.map (algebraTransition r s hs) (idealTransition r I)
  map_add' := map_add _
  map_smul' a z := by
    induction z with
    | tmul x y =>
      simp only [smul_tmul', TensorProduct.map_tmul, algebraTransition,
        LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, map_mul]
    | add x y hx hy =>
      simp only [smul_add, map_add, hx, hy]

@[simp]
lemma transition_tmul (I : Ideal R) (x : S) (a : I) :
    transition r s hs I (x ⊗ₜ[R] a) = s x ⊗ₜ[R'] idealTransition r I a := rfl

/-- The multiplication square commutes for every tensor, including kernel elements. -/
theorem inclusion_transition (I : Ideal R) (z : S ⊗[R] I) :
    FCurve.idealTensorInclusion (I.map r) (transition r s hs I z) =
      s (FCurve.idealTensorInclusion I z) := by
  induction z with
  | tmul x a =>
    simp only [transition_tmul, FCurve.idealTensorInclusion_tmul, map_mul]
    exact congrArg (fun b ↦ s x * b) (RingHom.congr_fun hs a).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- In particular the actual obstruction maps into the new obstruction. -/
theorem transition_mem_obstruction (I : Ideal R) (z : obstruction (S := S) I) :
    transition r s hs I z.val ∈ obstruction (S := S') (I.map r) := by
  change FCurve.idealTensorInclusion _ _ = 0
  rw [inclusion_transition, show FCurve.idealTensorInclusion I z.val = 0 from z.property,
    map_zero]

end FLT.Mazur.IdealTensorKernel
