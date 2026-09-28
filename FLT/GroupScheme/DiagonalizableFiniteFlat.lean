/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryD
public import FLT.GroupScheme.HopfPoints
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.Jacobson.Semiprimary
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# Finite diagonalizable group schemes

The group algebra of a finite abelian group is a finite-flat commutative,
cocommutative Hopf algebra. Over the rationals it is reduced by Maschke's
theorem and hence étale. This gives actual finite-flat models over `ℤ[1/2]`,
including the group of cube roots of unity.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

/-- Package a finite-flat Hopf algebra and its actual generic geometric points. -/
def FF.ofCoordinateRing {R : Type} [CommRing R] [Algebra R ℚ]
    (A : Type) [CommRing A] [HopfAlgebra R A] [HopfAlgebra.IsFiniteFlat R A]
    [Coalgebra.IsCocomm R A] [Algebra.Etale ℚ (ℚ ⊗[R] A)] : FF R := by
  letI := HopfAlgebra.pointsCommGroup ℚ (AlgebraicClosure ℚ) (ℚ ⊗[R] A)
  exact
  { points := { Carrier := Additive (ℚ ⊗[R] A →ₐ[ℚ] AlgebraicClosure ℚ) }
    model :=
      { CoordinateRing := A
        points :=
          { toFun := id
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
        points_bijective := Function.bijective_id } }

/-- A finite abelian group algebra over the rationals is étale. -/
theorem groupAlgebra_rational_etale (G : Type) [CommGroup G] [Finite G] :
    Algebra.Etale ℚ (MonoidAlgebra ℚ G) := by
  let : NeZero (Nat.card G : ℚ) :=
    ⟨by exact_mod_cast Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  exact Algebra.etale_of_finite_reduced ℚ (MonoidAlgebra ℚ G)

/-- The finite diagonalizable group scheme with the given finite character group. -/
def diagonalizableFiniteFlat (A : Type) [AddCommGroup A] [Finite A] : FF ZInvTwo := by
  let H := MonoidAlgebra ZInvTwo (Multiplicative A)
  letI : HopfAlgebra.IsFiniteFlat ZInvTwo H := ⟨⟩
  letI : Algebra.Etale ℚ (MonoidAlgebra ℚ (Multiplicative A)) :=
    groupAlgebra_rational_etale (Multiplicative A)
  letI : Algebra.Etale ℚ (ℚ ⊗[ZInvTwo] H) :=
    Algebra.Etale.of_equiv (MonoidAlgebra.scalarTensorEquiv ZInvTwo ℚ (M := Multiplicative A)).symm
  exact FF.ofCoordinateRing H

/-- The finite-flat group scheme of cube roots of unity over `ℤ[1/2]`,
represented by the group algebra of `ℤ/3ℤ`. -/
def muThree : FF ZInvTwo := diagonalizableFiniteFlat (ZMod 3)

end ThreeAdicPlan
