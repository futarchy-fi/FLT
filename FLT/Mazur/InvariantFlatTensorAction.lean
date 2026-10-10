/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupInvariantRing
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The action after base change of the invariant ring

The original action extends to the actual tensor-product algebra by fixing
its new scalar factor. The resulting fixed ring receives the canonical
map from the new base ring.
-/

@[expose] public noncomputable section

open TensorProduct

namespace FLT.Mazur.FiniteGroupQuotient

variable (G A : Type*) [Group G] [CommRing A] [MulSemiringAction G A]
variable (B : Type*) [CommRing B] [Algebra (invariantRing G A) B]

/-- The base-changed action on tensor-product coordinates. -/
def tensorActionHom (g : G) : (B ⊗[invariantRing G A] A) →ₐ[B] (B ⊗[invariantRing G A] A) :=
  Algebra.TensorProduct.map (AlgHom.id B B) (MulSemiringAction.toAlgHom (invariantRing G A) A g)

/-- The action fixes the scalar factor on pure tensors. -/
lemma tensorActionHom_tmul (g : G) (b : B) (a : A) :
    tensorActionHom G A B g (b ⊗ₜ[(invariantRing G A)] a) = b ⊗ₜ[(invariantRing G A)] (g • a) := rfl

/-- The tensor action respects the identity. -/
lemma tensorActionHom_one :
    tensorActionHom G A B 1 = AlgHom.id B (B ⊗[invariantRing G A] A) := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b a => simp only [tensorActionHom_tmul, one_smul, AlgHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The tensor action respects group multiplication. -/
lemma tensorActionHom_mul (g h : G) :
    tensorActionHom G A B (g * h) =
      (tensorActionHom G A B g).comp (tensorActionHom G A B h) := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b a => simp only [tensorActionHom_tmul, AlgHom.comp_apply, mul_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The genuine finite-group action on the base-changed ring. -/
@[instance_reducible]
def tensorAction : MulSemiringAction G (B ⊗[invariantRing G A] A) :=
  MulSemiringAction.compHom _
    ({ toFun := fun g ↦ (tensorActionHom G A B g).toRingHom
       map_one' := congrArg AlgHom.toRingHom (tensorActionHom_one G A B)
       map_mul' g h := congrArg AlgHom.toRingHom (tensorActionHom_mul G A B g h) } :
      G →* ((B ⊗[invariantRing G A] A) →+* (B ⊗[invariantRing G A] A)))

/-- The action fixes every new base scalar. -/
lemma tensorAction_algebraMap (g : G) (b : B) :
    let _ := tensorAction G A B
    g • algebraMap B (B ⊗[invariantRing G A] A) b =
      algebraMap B (B ⊗[invariantRing G A] A) b :=
  (tensorActionHom G A B g).commutes b

/-- The canonical map from the new base into the actual fixed ring. -/
def tensorInvariantMap :
    let _ := tensorAction G A B
    B →+* invariantRing G (B ⊗[invariantRing G A] A) := by
  let _ := tensorAction G A B
  exact lift G (B ⊗[invariantRing G A] A) (algebraMap B (B ⊗[invariantRing G A] A))
    (tensorAction_algebraMap G A B)

/-- The fixed-ring comparison retains the actual tensor-product coordinate map. -/
lemma tensorInvariantMap_val (b : B) :
    let _ := tensorAction G A B
    (tensorInvariantMap G A B b : (B ⊗[invariantRing G A] A)) =
      algebraMap B (B ⊗[invariantRing G A] A) b := rfl

/-- The tensor action agrees with the tensor of the original linear action. -/
lemma tensorActionHom_eq_lTensor (g : G) (x : (B ⊗[invariantRing G A] A)) :
    tensorActionHom G A B g x =
      (MulSemiringAction.toAlgHom (invariantRing G A) A g).toLinearMap.lTensor B x := by
  induction x using TensorProduct.inductionOn with
  | tmul b a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end FLT.Mazur.FiniteGroupQuotient
