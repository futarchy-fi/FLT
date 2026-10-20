/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableCoefficientReduction

/-!
# Naturality of the full character coefficient ideal

Every character substitution preserves the original coefficient reduction
kernel. In its ideal-valued coordinates it is exactly finite-support reindexing,
including substitutions that identify distinct characters.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DiagonalizableCobar

variable (R G H : Type*) [CommRing R] [AddCommMonoid G] [AddCommMonoid H]
  (I : Ideal R) (f : G →+ H)

/-- Character substitution preserves the full original infinitesimal ideal. -/
theorem mapDomain_mem_coefficientIdeal (p : AddMonoidAlgebra R G)
    (hp : p ∈ coefficientIdeal R G I) :
    AddMonoidAlgebra.mapDomainAlgHom R R f p ∈ coefficientIdeal R H I := by
  change coefficientReduction R H I _ = 0
  rw [coefficientReduction_mapDomain]
  change coefficientReduction R G I p = 0 at hp
  rw [hp, map_zero]

/-- Inserting ideal coefficients commutes with every actual character algebra map. -/
theorem fromIdealCoefficients_mapDomain (q : G →₀ I) :
    AddMonoidAlgebra.mapDomainAlgHom R R f (fromIdealCoefficients R G I q).val =
      (fromIdealCoefficients R H I (Finsupp.lmapDomain I R f q)).val := by
  apply AddMonoidAlgebra.coeff_injective
  exact Finsupp.mapDomain_mapRange f q (fun a : I ↦ a.val) rfl (fun _ _ ↦ rfl)

/-- The induced ideal map retains the full character algebra map. -/
def coefficientIdealMap : coefficientIdeal R G I →ₗ[R] coefficientIdeal R H I where
  toFun p := ⟨AddMonoidAlgebra.mapDomainAlgHom R R f p.val,
    mapDomain_mem_coefficientIdeal R G H I f p.val p.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The original ideal equivalence is natural under arbitrary character substitutions. -/
theorem idealCoefficientsEquiv_natural (q : G →₀ I) :
    coefficientIdealMap R G H I f (idealCoefficientsEquiv R G I q) =
      idealCoefficientsEquiv R H I (Finsupp.lmapDomain I R f q) := by
  apply Subtype.ext
  exact fromIdealCoefficients_mapDomain R G H I f q

end FLT.Mazur.DiagonalizableCobar
