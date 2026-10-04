/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltration
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A framing adapted to the actual ordinary quotient

Exactness constructs the frame from the injected unit vector and any lift of
one. The second coordinate is the original quotient map, even for a nonsplit
representation; no equivariant section is assumed.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions.OrdinaryFiltration
variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {α β : G →* kˣ} (E : OrdinaryFiltration ρ α β)

/-- Combine the actual sub-line and the chosen quotient lift. -/
def frameMap (w : V) : (Fin 2 → k) →ₗ[k] V :=
  E.injection.comp (LinearMap.proj 0) +
    (LinearMap.toSpanSingleton k V w).comp (LinearMap.proj 1)

/-- The original projection kills the injected line by exactness. -/
theorem projection_injection (a : k) : E.projection (E.injection a) = 0 := by
  have h : E.injection a ∈ LinearMap.range E.injection := ⟨a, rfl⟩
  rw [← E.exact] at h
  exact h

/-- The quotient coordinate of the constructed frame is its second coordinate. -/
theorem projection_frameMap (w : V) (hw : E.projection w = 1) (v : Fin 2 → k) :
    E.projection (E.frameMap w v) = v 1 := by
  change E.projection (E.injection (v 0) + v 1 • w) = v 1
  rw [map_add, E.projection_injection, map_smul, hw, zero_add, smul_eq_mul, mul_one]

/-- Exactness proves that the frame is a bijection, without a splitting premise. -/
theorem frameMap_bijective (w : V) (hw : E.projection w = 1) :
    Function.Bijective (E.frameMap w) := by
  constructor
  · intro v z h
    have h1 : v 1 = z 1 := by
      simpa only [E.projection_frameMap w hw] using congrArg E.projection h
    have h0 : v 0 = z 0 := by
      apply E.injective
      change E.injection (v 0) + v 1 • w = E.injection (z 0) + z 1 • w at h
      rw [h1] at h
      exact add_right_cancel h
    funext i
    fin_cases i <;> assumption
  · intro x
    have hx : x - E.projection x • w ∈ LinearMap.range E.injection := by
      rw [← E.exact]
      change E.projection (x - E.projection x • w) = 0
      simp [hw]
    obtain ⟨a, ha⟩ := hx
    refine ⟨![a, E.projection x], ?_⟩
    change E.injection a + E.projection x • w = x
    rw [ha]
    exact sub_add_cancel _ _

/-- The actual ordinary filtration determines an adapted linear frame. -/
def adaptedFrame (w : V) (hw : E.projection w = 1) : (Fin 2 → k) ≃ₗ[k] V :=
  LinearEquiv.ofBijective (E.frameMap w) (E.frameMap_bijective w hw)

/-- Inverse coordinates recover the original quotient functional. -/
theorem adaptedFrame_symm_one (w : V) (hw : E.projection w = 1) (x : V) :
    (E.adaptedFrame w hw).symm x 1 = E.projection x := by
  have h := E.projection_frameMap w hw ((E.adaptedFrame w hw).symm x)
  change E.projection (E.adaptedFrame w hw ((E.adaptedFrame w hw).symm x)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The residual action in this frame has the specified quotient character. -/
theorem adaptedFrame_action_one (w : V) (hw : E.projection w = 1) (g : G)
    (v : Fin 2 → k) :
    (E.adaptedFrame w hw).symm (ρ g (E.adaptedFrame w hw v)) 1 = (β g : k) * v 1 := by
  rw [E.adaptedFrame_symm_one, E.projection_equivariant]
  congr 1
  exact E.projection_frameMap w hw v

/-- The actual matrix in the adapted frame has the quotient row used by the local ideal. -/
theorem adaptedFrame_matrix_row (w : V) (hw : E.projection w = 1) (g : G) (j : Fin 2) :
    LinearMap.toMatrix' (((E.adaptedFrame w hw).symm.toLinearMap.comp (ρ g)).comp
      (E.adaptedFrame w hw).toLinearMap) 1 j = if j = 1 then (β g : k) else 0 := by
  rw [LinearMap.toMatrix'_apply]
  change (E.adaptedFrame w hw).symm (ρ g (E.adaptedFrame w hw (Pi.single j 1))) 1 = _
  rw [E.adaptedFrame_action_one]
  simp [Pi.single_apply, eq_comm]

end GaloisRepresentation.Extensions.OrdinaryFiltration
