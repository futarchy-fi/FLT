/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorCoefficientCartesian
public import FLT.Mazur.PolygonArithmeticResidueNilpotence

/-!
# Residue points cover every arithmetic tensor chart

If the parameter generates the maximal ideal, residue specialization is
surjective on every full tensor chart. Original affine functions have the
same vanishing tests at a point and any residue lift of it.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.PolygonArithmeticStages
universe u
variable (R : Type u) [CommRing R] [IsLocalRing R] (π : R)
  (hπ : algebraMap R (ResidueField R) π = 0) (m : ℕ)

/-- The arithmetic residue map preserves the original coefficient algebra. -/
def residueAlgHom : Quotient R π m →ₐ[R] ResidueField R :=
  { residueMap R π hπ m with commutes' := fun _ => rfl }

variable (A : Type u) [CommRing A] [Algebra R A]

/-- Specialization of the coefficient factor of the original full tensor chart. -/
def tensorResidue : Spec (.of (ResidueField R ⊗[R] A)) ⟶
    Spec (.of (Quotient R π m ⊗[R] A)) :=
  TensorCoefficientMap.spectrum (residueAlgHom R π hπ m)

/-- Nilpotent arithmetic thickening adds no points to the full affine tensor chart. -/
theorem tensorResidue_surjective (hgen : maximalIdeal R = ideal R π) :
    Surjective (tensorResidue R π hπ m A) := by
  let _ : Surjective (Spec.map (CommRingCat.ofHom
      (residueAlgHom R π hπ m).toRingHom)) := residueBase_surjective R π hgen hπ m
  exact TensorCoefficientMap.spectrum_surjective _

/-- Every arithmetic point admits a residue lift with precisely the same affine functions. -/
theorem exists_tensorResidue_lift (hgen : maximalIdeal R = ideal R π)
    (p : Spec (.of (Quotient R π m ⊗[R] A))) :
    ∃ q : Spec (.of (ResidueField R ⊗[R] A)), tensorResidue R π hπ m A q = p ∧
      ∀ a : A, (1 : Quotient R π m) ⊗ₜ[R] a ∈ p.asIdeal ↔
        (1 : ResidueField R) ⊗ₜ[R] a ∈ q.asIdeal := by
  let _ := tensorResidue_surjective R π hπ m A hgen
  obtain ⟨q, rfl⟩ := (tensorResidue R π hπ m A).surjective p
  exact ⟨q, rfl, fun a => TensorCoefficientMap.spectrum_tmul_mem _ a q⟩

/-- The full integral affine projection is unchanged by residue specialization. -/
@[reassoc] theorem tensorResidue_projection :
    tensorResidue R π hπ m A ≫ TensorOpenChart.projection =
      TensorOpenChart.projection := TensorCoefficientMap.spectrum_projection _

end FLT.Mazur.PolygonArithmeticStages
