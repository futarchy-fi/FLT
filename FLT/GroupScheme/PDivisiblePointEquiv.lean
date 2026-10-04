/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisiblePointColimit

/-! # Algebra equivalences act on the original point colimit -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (X : PDivisibleSystem R K p height)

/-- An equivalence of test algebras transports the original colimit points. -/
def pointColimitEquiv (e : B ≃ₐ[R] C) : X.PointColimit B ≃ X.PointColimit C where
  toFun := X.pointColimitMap e.toAlgHom
  invFun := X.pointColimitMap e.symm.toAlgHom
  left_inv x := by
    rw [← X.pointColimitMap_comp, AlgEquiv.symm_comp, X.pointColimitMap_id]
  right_inv x := by
    rw [← X.pointColimitMap_comp, AlgEquiv.comp_symm, X.pointColimitMap_id]

end ThreeAdicPlan.PDivisibleSystem
