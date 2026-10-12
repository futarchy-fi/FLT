/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicRelationFamilyIso

/-!
# Cocycle coherence of the actual full-family normalization comparisons

The comparisons over the represented relation are identities on the diagonal
and compose on triples. They retain the original families, not replacement models.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- The canonical relation comparison on the diagonal is the original family identity. -/
theorem cyclicRelationFamilyIso_refl (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    cyclicRelationFamilyIso n f f rfl = Iso.refl _ := by
  simp only [cyclicRelationFamilyIso_def, cyclicRelationNormalizedGroupIso_def,
    eqToIso_refl, Iso.refl_trans, Iso.symm_self_id]

/-- The actual original-family comparisons satisfy the cocycle equation. -/
theorem cyclicRelationFamilyIso_trans (f g k : T ⟶ (cyclicAuxiliaryScheme n).left)
    (h : cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g)
    (j : cyclicSchemeNormalizedPoint n g = cyclicSchemeNormalizedPoint n k) :
    cyclicRelationFamilyIso n f g h ≪≫ cyclicRelationFamilyIso n g k j =
      cyclicRelationFamilyIso n f k (h.trans j) := by
  apply Iso.ext
  simp only [cyclicRelationFamilyIso_def, cyclicRelationNormalizedGroupIso_def,
    Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, eqToIso.hom, eqToHom_trans_assoc]

/-- The reversed relation comparison is the inverse actual family isomorphism. -/
theorem cyclicRelationFamilyIso_symm (f g : T ⟶ (cyclicAuxiliaryScheme n).left)
    (h : cyclicSchemeNormalizedPoint n f = cyclicSchemeNormalizedPoint n g) :
    cyclicRelationFamilyIso n g f h.symm = (cyclicRelationFamilyIso n f g h).symm := by
  apply Iso.ext
  apply (cancel_epi (cyclicRelationFamilyIso n f g h).hom).mp
  have ht := congrArg Iso.hom (cyclicRelationFamilyIso_trans n f g f h h.symm)
  rw [cyclicRelationFamilyIso_refl] at ht
  exact ht.trans (cyclicRelationFamilyIso n f g h).hom_inv_id.symm

end FLT.Mazur.UniversalWeierstrass
