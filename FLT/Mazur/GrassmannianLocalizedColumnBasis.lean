/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSelectedColumnsLocalization

/-!
# From localized column maps to tensor quotient bases

A bijective localization of the selected column map constructs a basis in the
localized quotient and then in the tensor-extended quotient. These are bases of
the original quotient, with the same prescribed columns.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R Q : Type u} [CommRing R] [AddCommGroup Q] [Module R Q] {d : ℕ}

/-- A prescribed column family equal to a basis induces a bijective column map. -/
theorem selectedColumnMap_bijective_of_basis (v : Fin d → Q)
    (c : Module.Basis (Fin d) R Q) (hc : ∀ i, c i = v i) :
    Function.Bijective (selectedColumnMap (R := R) v) := by
  let b := Pi.basisFun R (Fin d)
  have h : selectedColumnMap v = (b.repr.trans c.repr.symm).toLinearMap := by
    apply b.ext
    intro i
    rw [selectedColumnMap, Module.Basis.constr_basis, ← hc]
    simp
  rw [h]
  exact (b.repr.trans c.repr.symm).bijective

/-- A localized column isomorphism transports the standard basis to the quotient. -/
def localizedColumnBasis (S : Submonoid R) (v : Fin d → Q)
    (h : Function.Bijective (LocalizedModule.map S (selectedColumnMap v))) :
    Module.Basis (Fin d) (Localization S) (LocalizedModule S Q) :=
  ((Pi.basisFun R (Fin d)).ofIsLocalizedModule (Localization S) S
    (LocalizedModule.mkLinearMap S (Fin d → R))).map (LinearEquiv.ofBijective _ h)

/-- The constructed localized basis consists of the same original columns. -/
theorem localizedColumnBasis_apply (S : Submonoid R) (v : Fin d → Q)
    (h : Function.Bijective (LocalizedModule.map S (selectedColumnMap v))) (i : Fin d) :
    localizedColumnBasis S v h i = LocalizedModule.mkLinearMap S Q (v i) := by
  change LocalizedModule.map S (selectedColumnMap v)
    ((Pi.basisFun R (Fin d)).ofIsLocalizedModule (Localization S) S
      (LocalizedModule.mkLinearMap S (Fin d → R)) i) = _
  exact selectedColumnMap_localized_basis S v i

/-- Tensor extension of the constructed basis of the original localized quotient. -/
def tensorLocalizedColumnBasis (S : Submonoid R) (v : Fin d → Q)
    (h : Function.Bijective (LocalizedModule.map S (selectedColumnMap v))) :
    Module.Basis (Fin d) (Localization S) (Localization S ⊗[R] Q) :=
  (localizedColumnBasis S v h).map (LocalizedModule.equivTensorProduct S Q)

/-- The tensor basis retains the exact original quotient columns. -/
theorem tensorLocalizedColumnBasis_apply (S : Submonoid R) (v : Fin d → Q)
    (h : Function.Bijective (LocalizedModule.map S (selectedColumnMap v))) (i : Fin d) :
    tensorLocalizedColumnBasis S v h i = 1 ⊗ₜ[R] v i := by
  change LocalizedModule.equivTensorProduct S Q (localizedColumnBasis S v h i) = _
  rw [localizedColumnBasis_apply]
  simp only [LocalizedModule.mkLinearMap_apply, LocalizedModule.equivTensorProduct_apply_mk,
    Localization.mk_one_eq_algebraMap, map_one]

/-- The normalized selected map into the tensor quotient is an actual isomorphism. -/
theorem tensorLocalizedColumnMap_bijective (S : Submonoid R) (v : Fin d → Q)
    (h : Function.Bijective (LocalizedModule.map S (selectedColumnMap v))) :
    Function.Bijective (selectedColumnMap (R := Localization S)
      (fun i ↦ (1 : Localization S) ⊗ₜ[R] v i)) :=
  selectedColumnMap_bijective_of_basis _ (tensorLocalizedColumnBasis S v h)
    (tensorLocalizedColumnBasis_apply S v h)

end FLT.Mazur.GrassmannianChart
