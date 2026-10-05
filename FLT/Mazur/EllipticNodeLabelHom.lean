/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeLabelAdditivity

/-!
# Additive nodal labels and the actual component quotient

The proved addition law packages the point label as a homomorphism with
kernel E₀. Its canonical quotient descent is an injective additive map
into Z/nZ. No additivity or component classification is supplied as data.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)

/-- The canonical nodal label, with its proved addition law. -/
noncomputable def nodePointLabelHom : (W.map (algebraMap A K)).toProjective.Point →+ ZMod n where
  toFun := nodePointLabel D
  map_zero' := nodePointLabel_zero D
  map_add' := nodePointLabel_add D

/-- The homomorphism evaluates to the original point label. -/
@[simp] theorem nodePointLabelHom_apply (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointLabelHom D P = nodePointLabel D P := rfl

/-- The kernel is exactly the actual smooth-reduction subgroup. -/
theorem nodePointLabelHom_ker : (nodePointLabelHom D).ker = ellipticE0 A W := by
  ext P
  exact nodePointLabel_eq_zero_iff_mem D P

/-- Addition of actual component classes adds their descended labels. -/
theorem nodeComponentLabel_add (c d : EllipticComponentQuotient A W) :
    nodeComponentLabel D (c + d) = nodeComponentLabel D c + nodeComponentLabel D d := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  obtain ⟨Q, rfl⟩ := ellipticComponentHom_surjective A W d
  rw [← map_add, nodeComponentLabel_mk, nodeComponentLabel_mk, nodeComponentLabel_mk]
  exact nodePointLabel_add D P Q

/-- The canonical injection from actual component classes, now as an additive map. -/
noncomputable def nodeComponentLabelHom : EllipticComponentQuotient A W →+ ZMod n where
  toFun := nodeComponentLabel D
  map_zero' := nodeComponentLabel_zero D
  map_add' := nodeComponentLabel_add D

/-- The component homomorphism evaluates to the canonical quotient label. -/
@[simp] theorem nodeComponentLabelHom_apply (c : EllipticComponentQuotient A W) :
    nodeComponentLabelHom D c = nodeComponentLabel D c := rfl

/-- The additive component-label map is injective. -/
theorem nodeComponentLabelHom_injective : Function.Injective (nodeComponentLabelHom D) :=
  nodeComponentLabel_injective D

/-- The point label factors through the actual quotient map. -/
theorem nodeComponentLabelHom_comp :
    (nodeComponentLabelHom D).comp (ellipticComponentHom A W) = nodePointLabelHom D := rfl

include D

/-- Multiplication by the nodal depth kills every actual component class. -/
theorem nodeComponent_nsmul_depth (c : EllipticComponentQuotient A W) : n • c = 0 := by
  apply nodeComponentLabelHom_injective D
  rw [map_nsmul, map_zero]
  simp [nsmul_eq_mul]

/-- Multiplication by the nodal depth sends every generic point into E₀. -/
theorem smoothReduction_nsmul_node_depth (P : (W.map (algebraMap A K)).toProjective.Point) :
    SmoothReduction A W (n • P) := by
  rw [← ellipticComponentHom_eq_zero, map_nsmul]
  exact nodeComponent_nsmul_depth D _

end FLT.Mazur
