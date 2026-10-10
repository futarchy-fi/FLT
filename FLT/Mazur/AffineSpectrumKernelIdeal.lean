/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicThickening

/-!
# The defining ideal of an affine spectrum map

The scheme-theoretic kernel of Spec of a ring map is the ideal sheaf of its
actual ring kernel. The comparison retains the canonical spectrum coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.BaseAdicThickening

set_option backward.isDefEq.respectTransparency false

variable {R S : CommRingCat} (f : R ⟶ S)

/-- The actual ring kernel is the defining ideal sheaf of the spectrum morphism. -/
theorem specMap_ker_baseIdeal :
    (Spec.map f).ker = baseIdeal R (RingHom.ker f.hom) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply, baseIdeal_top]
  ext s
  change (Spec.map f).appTop s = 0 ↔
    s ∈ (RingHom.ker f.hom).map (Scheme.ΓSpecIso R).inv.hom
  rw [Ideal.mem_map_iff_of_surjective (Scheme.ΓSpecIso R).inv.hom
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.surjective]
  constructor
  · intro hs
    refine ⟨(Scheme.ΓSpecIso R).hom s, ?_, ?_⟩
    · have he := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality f) s
      change (Scheme.ΓSpecIso S).hom ((Spec.map f).appTop s) =
        f ((Scheme.ΓSpecIso R).hom s) at he
      rw [hs, map_zero] at he
      exact he.symm
    · exact (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm_apply_apply s
  · rintro ⟨r, hr, rfl⟩
    have he := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality f) r
    change (Scheme.ΓSpecIso S).inv (f r) =
      (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv r) at he
    change f r = 0 at hr
    rw [hr, map_zero] at he
    exact he.symm

end FLT.Mazur.BaseAdicThickening
