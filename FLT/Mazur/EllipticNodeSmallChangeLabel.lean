/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeChangeCoordinates

/-!
# Label comparison for branch-preserving integral changes

Between finite-depth split models, unit scaling and sufficiently deep
translations preserve the signed component label when the shear reduces
to zero. The result allows different uniformizers in the two models.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} [(W.map (algebraMap A K)).IsElliptic]
  {π π' : A} {n : ℕ} (D : SplitNodeDepth W π n) (C : VariableChange A)
  (D' : SplitNodeDepth (C • W) π' n)

/-- Small shears and deep translations preserve the actual point label. -/
theorem nodePointLabel_smallChange (hs : C.s ∈ maximalIdeal A)
    (hr : C.r ∈ maximalIdeal A ^ (n + 1)) (ht : C.t ∈ maximalIdeal A ^ (n + 1))
    (P : ((C • W).map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D (integralProjectiveVariableChange A W C P) = nodePointLabel D' P := by
  let D'' : SplitNodeDepth (C • W) π n :=
    { D' with uniformizer_ne_zero := D.uniformizer_ne_zero, maximalIdeal_eq := D.maximalIdeal_eq }
  rw [← nodePointLabel_uniformizer_independent D' D'' P]
  by_cases hp : SmoothReduction A (C • W) P
  · rw [(nodePointLabel_eq_zero_iff D'' P).mpr hp,
      (nodePointLabel_eq_zero_iff D _).mpr
        ((integralProjectiveVariableChange_smooth A W C P).mpr hp)]
  · obtain ⟨v, hv⟩ := exists_nodePointCoordinates A (C • W) π D.maximalIdeal_eq n
      D'.a₃_mem D'.a₄_mem D'.a₆_not_mem P hp
    obtain ⟨ρ, hρ, hr'⟩ := exists_node_deep_factor D.maximalIdeal_eq v.depth
      (Ideal.pow_le_pow_right (by omega) hr)
    obtain ⟨τ, hτ, ht'⟩ := exists_node_deep_factor D.maximalIdeal_eq v.depth
      (Ideal.pow_le_pow_right (by omega) ht)
    obtain ⟨w, _, hw⟩ := exists_nodePointCoordinates_smallChange C v hs hρ hτ hr' ht'
    rw [nodePointLabel_eq_of_coordinates D w, nodePointLabel_eq_of_coordinates D'' v]
    exact hw

/-- Small shears and deep translations preserve the actual component label. -/
theorem nodeComponentLabel_smallChange (hs : C.s ∈ maximalIdeal A)
    (hr : C.r ∈ maximalIdeal A ^ (n + 1)) (ht : C.t ∈ maximalIdeal A ^ (n + 1))
    (c : EllipticComponentQuotient A (C • W)) :
    nodeComponentLabel D (integralComponentVariableChange A W C c) = nodeComponentLabel D' c := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A (C • W) c
  rw [integralComponentVariableChange_mk, nodeComponentLabel_mk, nodeComponentLabel_mk]
  exact nodePointLabel_smallChange D C D' hs hr ht P

/-- Pure unit scaling preserves point labels, independently of the uniformizer. -/
theorem nodePointLabel_unitScale (u : Aˣ)
    (Du : SplitNodeDepth ((VariableChange.mk u 0 0 0 : VariableChange A) • W) π' n)
    (P : (((VariableChange.mk u 0 0 0 : VariableChange A) • W).map
      (algebraMap A K)).toProjective.Point) :
    nodePointLabel D (integralProjectiveVariableChange A W (.mk u 0 0 0) P) =
      nodePointLabel Du P :=
  nodePointLabel_smallChange D (.mk u 0 0 0) Du (Ideal.zero_mem _) (Ideal.zero_mem _)
    (Ideal.zero_mem _) P

end FLT.Mazur
