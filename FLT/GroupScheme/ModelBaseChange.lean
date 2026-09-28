/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.BialgebraBaseChange
public import FLT.GroupScheme.FiniteFlatDifferentials
public import FLT.GroupScheme.GenericFieldChange

/-!
# Base change of chosen finite flat models

Scalar extension of the coordinate Hopf algebra models the restricted Galois
module. In particular, an integer annihilating the original geometric points
also annihilates the points after base change.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.HasFiniteFlatModel

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {W : FiniteContinuousGaloisModule K}

/-- Forget the bundled Galois module while retaining its model and point comparison. -/
def toFF (M : HasFiniteFlatModel R W) : FF R K where
  CoordinateRing := M.CoordinateRing
  Points := W
  points := M.points
  points_bijective := M.points_bijective

/-- The annihilation condition on the model is the one on its specified point group. -/
@[simp] theorem killedBy_toFF (M : HasFiniteFlatModel R W) (n : ℕ) :
    KilledBy n M.toFF ↔ ∀ w : W, n • w = 0 := Iff.rfl

variable (S L : Type) [CommRing S] [Field L] [PerfectField K] [PerfectField L]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L]
  [Algebra K L] [IsScalarTower R K L]

/-- The generic fibre of the scalar-extended coordinate algebra is the coordinate
algebra of the restricted Galois module. -/
def baseChangeGenericBialgEquiv (M : HasFiniteFlatModel R W) :
    L ⊗[S] (S ⊗[R] M.CoordinateRing) ≃ₐc[L]
      (W.restrict (algebraMap K L)).GenericCoordinateAlgebra :=
  (bialgebraCancelBaseChange R S L M.CoordinateRing).trans
    ((bialgebraCancelBaseChange R K L M.CoordinateRing).symm.trans
      ((bialgebraBaseChangeEquiv K L _ _ M.genericBialgEquiv.symm).trans
        W.genericFieldChangeBialgEquiv))

/-- Base change of a chosen finite flat model, with the actual tensor-product
coordinate ring and the restricted action on the same finite abelian group. -/
def baseChange (M : HasFiniteFlatModel R W) :
    HasFiniteFlatModel S (W.restrict (algebraMap K L)) := by
  let A := S ⊗[R] M.CoordinateRing
  let : HopfAlgebra.IsFiniteFlat S A := ⟨⟩
  exact ofGenericBialgEquiv _ A (M.baseChangeGenericBialgEquiv S L)

/-- Base change preserves annihilation by any integer, without increasing the exponent. -/
theorem killedBy_baseChange (M : HasFiniteFlatModel R W) (n : ℕ)
    (h : KilledBy n M.toFF) : KilledBy n (M.baseChange S L).toFF := h

end ThreeAdicPlan.HasFiniteFlatModel
