/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.BialgebraBaseChange
public import FLT.GroupScheme.GenericFieldChange

/-!
# Scalar extension of a chosen finite-flat model

Integral scalar extension and generic field restriction retain the prescribed
Galois module, via the generic coordinate bialgebra comparison.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

/-- Extend a chosen integral model and restrict its geometric Galois module
along a compatible extension of fraction fields. -/
def HasFiniteFlatModel.scalarBaseChange {R S K L : Type}
    [CommRing R] [CommRing S] [Field K] [Field L] [PerfectField K] [PerfectField L]
    [Algebra R S] [Algebra R K] [Algebra K L] [Algebra S L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    {W : FiniteContinuousGaloisModule K} (M : HasFiniteFlatModel R W) :
    HasFiniteFlatModel S (W.restrict (algebraMap K L)) := by
  let A := S ⊗[R] M.CoordinateRing
  let instFiniteFlatA : HopfAlgebra.IsFiniteFlat S A := ⟨⟩
  let e : L ⊗[S] A ≃ₐc[L] (W.restrict (algebraMap K L)).GenericCoordinateAlgebra :=
    (bialgebraCancelBaseChange R S L M.CoordinateRing).trans
      ((bialgebraCancelBaseChange R K L M.CoordinateRing).symm.trans
        ((bialgebraBaseChangeEquiv K L _ _ M.genericBialgEquiv.symm).trans
          W.genericFieldChangeBialgEquiv))
  exact HasFiniteFlatModel.ofGenericBialgEquiv _ A e

end ThreeAdicPlan
