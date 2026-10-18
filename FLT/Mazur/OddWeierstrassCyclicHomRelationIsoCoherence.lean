/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationRelationIso

/-!
# Cocycle coherence of the actual full-family normalization comparisons

The comparisons over the represented relation are identities on the diagonal
and compose on triples. They retain the original families, not replacement models.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme}

/-- The canonical relation comparison on the diagonal is the original family identity. -/
theorem cyclicHomNormalizationRelationIso_refl (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) :
    cyclicHomNormalizationRelationIso n f f rfl = Iso.refl _ := by
  simp only [cyclicHomNormalizationRelationIso_def, cyclicHomParameterGroupIso_def,
    eqToIso_refl, Iso.refl_trans, Iso.symm_self_id]

/-- The actual original-family comparisons satisfy the cocycle equation. -/
theorem cyclicHomNormalizationRelationIso_trans (f g k : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g)
    (j : cyclicHomNormalizedPoint n g = cyclicHomNormalizedPoint n k) :
    cyclicHomNormalizationRelationIso n f g h ≪≫ cyclicHomNormalizationRelationIso n g k j =
      cyclicHomNormalizationRelationIso n f k (h.trans j) := by
  apply Iso.ext
  simp only [cyclicHomNormalizationRelationIso_def, cyclicHomParameterGroupIso_def,
    Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, eqToIso.hom, eqToHom_trans_assoc]

/-- The reversed relation comparison is the inverse actual family isomorphism. -/
theorem cyclicHomNormalizationRelationIso_symm (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : cyclicHomNormalizedPoint n f = cyclicHomNormalizedPoint n g) :
    cyclicHomNormalizationRelationIso n g f h.symm =
      (cyclicHomNormalizationRelationIso n f g h).symm := by
  apply Iso.ext
  apply (cancel_epi (cyclicHomNormalizationRelationIso n f g h).hom).mp
  have ht := congrArg Iso.hom (cyclicHomNormalizationRelationIso_trans n f g f h h.symm)
  rw [cyclicHomNormalizationRelationIso_refl] at ht
  exact ht.trans (cyclicHomNormalizationRelationIso n f g h).hom_inv_id.symm

end FLT.Mazur.OddWeierstrassParameter
