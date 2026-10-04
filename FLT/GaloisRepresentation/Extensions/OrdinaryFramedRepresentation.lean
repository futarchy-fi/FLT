/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryAdaptedFrame
public import FLT.Deformations.DeSmitLenstra.ProfiniteUniversalLift

/-!
# The continuous matrix representation in an ordinary adapted frame

The residual quotient row is derived from exactness of the original filtration.
The matrix representation is suitable for the actual universal framed ring.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions.OrdinaryFiltration
variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {α β : G →* kˣ} (E : OrdinaryFiltration ρ α β)
  (w : V) (hw : E.projection w = 1)

/-- The actual matrix representation after the constructed change of frame. -/
def adaptedMatrixRepresentation : G →* GL (Fin 2) k :=
  (Units.map (((E.adaptedFrame w hw).symm.conjAlgEquiv k).trans
    LinearMap.toMatrixAlgEquiv').toMonoidHom).comp ρ.asGroupHom

/-- Matrix entries are coordinates of the original representation action. -/
theorem adaptedMatrixRepresentation_apply (g : G) (i j : Fin 2) :
    E.adaptedMatrixRepresentation w hw g i j =
      (E.adaptedFrame w hw).symm (ρ g (E.adaptedFrame w hw (Pi.single j 1))) i := rfl

/-- The residual quotient row is proved, not assumed as framing data. -/
theorem adaptedMatrixRepresentation_row (g : G) (j : Fin 2) :
    E.adaptedMatrixRepresentation w hw g 1 j = if j = 1 then (β g : k) else 0 := by
  rw [E.adaptedMatrixRepresentation_apply, E.adaptedFrame_action_one]
  simp [Pi.single_apply, eq_comm]

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace V] [DiscreteTopology V]
  (hρ : ∀ x : V, Continuous (fun g : G ↦ ρ g x))

include hρ
omit [DiscreteTopology k] in
/-- Continuity follows from the original orbit maps, including the inverse matrices. -/
theorem adaptedMatrixRepresentation_continuous :
    Continuous (E.adaptedMatrixRepresentation w hw) := by
  rw [Units.continuous_iff]
  constructor
  · apply continuous_matrix
    intro i j
    change Continuous (fun g : G ↦ E.adaptedMatrixRepresentation w hw g i j)
    simp only [E.adaptedMatrixRepresentation_apply]
    exact (continuous_of_discreteTopology :
      Continuous (fun x : V ↦ (E.adaptedFrame w hw).symm x i)).comp
        (hρ (E.adaptedFrame w hw (Pi.single j 1)))
  · apply continuous_matrix
    intro i j
    have h : (fun g : G ↦ ((E.adaptedMatrixRepresentation w hw g)⁻¹).val i j) =
        fun g ↦ E.adaptedMatrixRepresentation w hw g⁻¹ i j := by
      funext g
      rw [map_inv]
    rw [h]
    simp only [E.adaptedMatrixRepresentation_apply]
    exact (continuous_of_discreteTopology :
      Continuous (fun x : V ↦ (E.adaptedFrame w hw).symm x i)).comp
        ((hρ (E.adaptedFrame w hw (Pi.single j 1))).comp continuous_inv)

/-- The continuous residual matrix representation for the universal deformation construction. -/
def adaptedContinuousMatrixRepresentation : G →ₜ* GL (Fin 2) k :=
  ⟨E.adaptedMatrixRepresentation w hw, E.adaptedMatrixRepresentation_continuous w hw hρ⟩

end GaloisRepresentation.Extensions.OrdinaryFiltration
