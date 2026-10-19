/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIsoFaithful

/-!
# Transporting prescribed compatible comparisons through presentations

Changing both full subgroup presentations preserves the existence and uniqueness
of an extension of a prescribed full curve comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {n : ℕ} {E F E' F' : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}
  {H' : E'.FiniteSubgroup n} {J' : F'.FiniteSubgroup n}

/-- Compatible changes of presentation transport all compatible comparisons bijectively. -/
def compatibleIsoCongr (a : CompatibleIso H H') (b : CompatibleIso J J') :
    CompatibleIso H J ≃ CompatibleIso H' J' where
  toFun e := a.symm.trans (e.trans b)
  invFun e := a.trans (e.trans b.symm)
  left_inv e := by
    apply CompatibleIso.ext_curve
    change a.curve ≪≫ (a.curve.symm ≪≫ (e.curve ≪≫ b.curve)) ≪≫ b.curve.symm = _
    simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]
  right_inv e := by
    apply CompatibleIso.ext_curve
    change a.curve.symm ≪≫ (a.curve ≪≫ (e.curve ≪≫ b.curve.symm)) ≪≫ b.curve = _
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- Extending a specified full curve map is independent of compatible presentations. -/
theorem compatibleIso_exists_conjugate_iff (a : CompatibleIso H H')
    (b : CompatibleIso J J') (e : E ≅ F) :
    (∃ d : CompatibleIso H J, d.curve = e) ↔
      ∃ d : CompatibleIso H' J', d.curve = a.curve.symm ≪≫ e ≪≫ b.curve := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨a.symm.trans (d.trans b), congrArg (fun z ↦ a.curve.symm ≪≫ z ≪≫ b.curve) hd⟩
  · rintro ⟨d, hd⟩
    refine ⟨a.trans (d.trans b.symm), ?_⟩
    change a.curve ≪≫ d.curve ≪≫ b.curve.symm = e
    rw [hd]
    simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
