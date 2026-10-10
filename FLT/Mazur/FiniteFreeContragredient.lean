/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Contragredient changes of finite free coordinates

Dual coordinates transform by the inverse transpose. The construction uses the
actual linear dual and the dual of the standard basis, so its convention is
fixed by evaluation rather than by a point-coordinate assertion about Proj.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.FiniteFreeContragredient
variable {R : Type u} [CommRing R] {ι κ ν : Type u}
    [Finite ι] [Finite κ] [Finite ν]

/-- The standard dual basis identifies a finite free module with its linear dual. -/
def dualCoordinates (R : Type u) [CommRing R] (ι : Type u) [Finite ι] :
    (ι →₀ R) ≃ₗ[R] Module.Dual R (ι →₀ R) := by
  classical
  exact (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R)).dualBasis.repr.symm

/-- The inverse transpose of a finite free change of coordinates. -/
def map (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) : (ι →₀ R) ≃ₗ[R] (κ →₀ R) :=
  (dualCoordinates R ι).trans (e.symm.dualMap.trans (dualCoordinates R κ).symm)

/-- Evaluating the standard dual coordinates on a generator recovers its coefficient. -/
@[simp]
lemma dualCoordinates_single (v : ι →₀ R) (i : ι) :
    dualCoordinates R ι v (Finsupp.single i 1) = v i := by
  classical
  have h := congrArg (fun w : ι →₀ R ↦ w i)
    ((Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R)).dualBasis.repr.apply_symm_apply v)
  simpa [dualCoordinates] using h

/-- A dual basis vector evaluates the corresponding original coordinate. -/
@[simp]
lemma dualCoordinates_single_left (i : ι) (r : R) (w : ι →₀ R) :
    dualCoordinates R ι (Finsupp.single i r) w = r * w i := by
  classical
  simp [dualCoordinates, Finsupp.basisSingleOne]

/-- Dual transport preserves the pairing with the original coordinate transport. -/
lemma pairing (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (v w : ι →₀ R) :
    dualCoordinates R κ (map e v) (e w) = dualCoordinates R ι v w := by
  simp [map, LinearEquiv.dualMap_apply]

/-- The coordinates of the dual change are obtained by evaluating on inverse generators. -/
lemma map_apply (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (v : ι →₀ R) (j : κ) :
    map e v j = dualCoordinates R ι v (e.symm (Finsupp.single j 1)) := by
  rw [← dualCoordinates_single]
  simp [map, LinearEquiv.dualMap_apply]

/-- On generators the dual coordinate matrix is precisely the inverse transpose. -/
lemma map_single (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (i : ι) (j : κ) :
    map e (Finsupp.single i 1) j = e.symm (Finsupp.single j 1) i := by
  rw [map_apply, dualCoordinates_single_left, one_mul]

/-- The contragredient of the identity is the identity. -/
@[simp]
lemma map_refl : map (LinearEquiv.refl R (ι →₀ R)) = LinearEquiv.refl R (ι →₀ R) := by
  ext v
  simp [map, LinearEquiv.dualMap_refl]

/-- Contragredient changes compose in the same order as the original changes. -/
lemma map_trans (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (d : (κ →₀ R) ≃ₗ[R] (ν →₀ R)) :
    (map e).trans (map d) = map (e.trans d) := by
  ext v
  simp [map, ← LinearEquiv.dualMap_trans]

/-- Inverting a chart change also inverts its contragredient. -/
lemma map_symm (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) : (map e).symm = map e.symm := by
  ext v
  simp [map, LinearEquiv.trans_symm, LinearEquiv.dualMap_symm]

end FLT.Mazur.FiniteFreeContragredient
