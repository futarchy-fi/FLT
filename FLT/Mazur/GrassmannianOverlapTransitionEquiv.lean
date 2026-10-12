/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianLocalizedAmbientTransition
public import FLT.Mazur.GrassmannianAmbientTransitionNaturality

/-!
# Inverse algebra maps between determinant overlaps

The transition maps on the two localized coordinate rings are mutually inverse.
The proof uses rational specialization and the inverse ambient change, then the
universal properties of the polynomial algebra and the principal localization.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
  (e : ((Fin d → R) × (κ → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))

/-- The two localized transitions recover all universal coordinate entries. -/
theorem ambientOverlapTransitionHom_matrix_comp :
    ((ambientOverlapMatrix e).map (ambientOverlapTransitionHom e.symm)).map
      (ambientOverlapTransitionHom e) = ambientOverlapMatrix e := by
  have h := ambientOverlapTransitionHom_matrix e.symm
  simp only [LinearEquiv.symm_symm] at h
  rw [h, ambientTransitionMatrix_algHom _ _ _ (ambientOverlapMatrix_isUnit e.symm),
    ambientOverlapTransitionHom_matrix, ambientEquivBaseChange_symm,
    ambientTransitionMatrix_symm _ _ (ambientOverlapMatrix_isUnit e)]

/-- The reverse and forward maps compose to the identity on the entire localization. -/
theorem ambientOverlapTransitionHom_comp :
    (ambientOverlapTransitionHom e).comp (ambientOverlapTransitionHom e.symm) =
      AlgHom.id R (ambientOverlapRing e) := by
  apply IsLocalization.algHom_ext (L := ambientOverlapRing e)
    (Submonoid.powers (overlapPolynomial (ambientBlockP e.toLinearMap)
      (ambientBlockQ e.toLinearMap)))
  apply MvPolynomial.algHom_ext
  intro ij
  exact congrArg (fun M ↦ M ij.1 ij.2) (ambientOverlapTransitionHom_matrix_comp e)

/-- The two determinant-localized algebras are isomorphic by the actual rational transitions. -/
def ambientOverlapTransitionEquiv : ambientOverlapRing e.symm ≃ₐ[R] ambientOverlapRing e :=
  AlgEquiv.ofAlgHom (ambientOverlapTransitionHom e) (ambientOverlapTransitionHom e.symm)
    (ambientOverlapTransitionHom_comp e)
    (by simpa only [LinearEquiv.symm_symm] using ambientOverlapTransitionHom_comp e.symm)

/-- The algebra isomorphism has the constructed forward transition as its homomorphism. -/
theorem ambientOverlapTransitionEquiv_toAlgHom :
    (ambientOverlapTransitionEquiv e).toAlgHom = ambientOverlapTransitionHom e := rfl

/-- Its inverse homomorphism is precisely the transition for the inverse ambient change. -/
theorem ambientOverlapTransitionEquiv_symm_toAlgHom :
    (ambientOverlapTransitionEquiv e).symm.toAlgHom = ambientOverlapTransitionHom e.symm := rfl

end FLT.Mazur.GrassmannianChart
