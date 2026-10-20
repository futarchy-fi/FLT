/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFormallySmoothStages
public import FLT.Mazur.OneGonNilpotentSurjectiveHomLift

/-!
# Original character groups and smooth curves at positive adic orders

The parameter at each positive order is nilpotent. The genuine adjacent
quotient map identifies the reduced cubic with the preceding original cubic,
without changing either the coefficient rings or the character source.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart WeierstrassDividedDepth
open CharacterSchemeBaseChange AdicFormallySmoothStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) (t : R)

/-- The original positive-order quotient ring. -/
abbrev StageRing (m : ℕ) := R ⧸ I ^ (m + 1)

/-- The actual smoothing parameter at a positive adic order. -/
def parameter (m : ℕ) : StageRing I m := Ideal.Quotient.mk _ t

/-- A parameter in the defining ideal is nilpotent at every positive order. -/
theorem parameter_nilpotent (ht : t ∈ I) (m : ℕ) : IsNilpotent (parameter I t m) := by
  refine ⟨m + 1, ?_⟩
  rw [parameter, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow ht _

/-- Adjacent reduction preserves the actual smoothing parameter. -/
theorem restriction_parameter (m : ℕ) :
    restriction I m (parameter I t (m + 1)) = parameter I t m := rfl

/-- The original smooth commutative group at a positive adic order. -/
def stageGroup (m : ℕ) : CommGrp (Over (Spec (.of (StageRing I m)))) :=
  integralSmoothGroup (equation (parameter I t m))

/-- The original full character group at that same order. -/
def stageSource (G : Type) [AddCommGroup G] (m : ℕ) :
    CommGrp (Over (Spec (.of (StageRing I m)))) := CommGrp.mk (model (StageRing I m) G)

/-- The coefficient map on the complete character algebra, retaining every character. -/
def characterRestriction (G : Type) [AddCommGroup G] (m : ℕ) :
    AddMonoidAlgebra (StageRing I (m + 1)) G →+* AddMonoidAlgebra (StageRing I m) G :=
  AddMonoidAlgebra.mapRingHom G (restriction I m).toRingHom

/-- The adjacent quotient map identifies the actual two cubic equations. -/
theorem restriction_equation (m : ℕ) :
    (equation (parameter I t (m + 1))).map (restriction I m).toRingHom =
      equation (parameter I t m) := by
  rw [equation_map]
  rfl

/-- The actual smooth-group comparison across the original adjacent quotient map. -/
def smoothRestriction (m : ℕ) : (stageGroup I t m).X.left ⟶
    (stageGroup I t (m + 1)).X.left := by
  letI := (restriction I m).toRingHom.toAlgebra
  exact (eqToHom (congrArg integralSmoothGroup
      (restriction_equation I t m).symm)).hom.hom.hom.left ≫
    originalSmoothCoefficientMap (StageRing I m) (equation (parameter I t (m + 1)))

end FLT.Mazur.OneGonAdicCharacterTower
