/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedSubgroup
public import FLT.Mazur.GeneralizedCurveBaseChangeTowerMap

/-!
# Actual shared-stage comparisons under extension of the finite ring

The literal inclusion of shared subalgebras gives the full curve tower
comparison. The intrinsic embedding tower equation is a separate construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

/-- The actual algebra structure of an inclusion of shared finite rings. -/
@[instance_reducible]
def sharedRingAlgebra (K L : Subalgebra ℤ R) (hKL : K ≤ L) : Algebra K L :=
  (Subalgebra.inclusion hKL).toAlgebra

/-- The actual spectrum map of an inclusion of shared finite rings. -/
def sharedRingMap (K L : Subalgebra ℤ R) (hKL : K ≤ L) : Spec (.of L) ⟶ Spec (.of K) :=
  @baseMap K L _ _ (sharedRingAlgebra K L hKL)

variable (I : Ideal R) [IsAdicComplete I R] (t : R) (ht : t ∈ I)
  (n : ℕ) [NeZero n] (s : Set R)
  (K L : Subalgebra ℤ R) [Algebra.FiniteType ℤ K] [Algebra.FiniteType ℤ L]
  (hS : base I t ht n s ≤ K) (hKL : K ≤ L) (hs : complementaryInverse I t ht ∈ s)

/-- The larger actual stage is the full pullback of the smaller shared-stage curve. -/
irreducible_def sharedCurveTowerIso :
    stageCurve I t ht n s (sharedStage I t ht n s L (hS.trans hKL)) hs ≅
      (stageCurve I t ht n s (sharedStage I t ht n s K hS) hs).baseChange
        (sharedRingMap K L hKL) := by
  let _ := sharedAlgebra I t ht n s K hS
  let _ := sharedAlgebra I t ht n s L (hS.trans hKL)
  let _ := sharedRingAlgebra K L hKL
  let _ : IsScalarTower (base I t ht n s) K L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (curve I t ht n s hs).baseChangeCompEqIso
    (baseMap (base I t ht n s) K) (baseMap K L) (baseMap (base I t ht n s) L)
    (characterTower_baseMap (base I t ht n s) K L).symm

end FLT.Mazur.OneGonAdicIndependentModel
