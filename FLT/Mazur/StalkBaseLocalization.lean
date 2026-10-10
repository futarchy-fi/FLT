/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StalkBaseClosedFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Localization.Basic

/-!
# Localization coordinates for base change to a stalk

On an affine base, the global coordinate map of the local-ring spectrum
is localization at the chosen point. This also proves flatness of the
actual canonical map to the base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.StalkBase

variable (S : Scheme.{u}) [IsAffine S] (s : S)

/-- The point's prime ideal in the actual global coordinate ring. -/
abbrev pointIdeal : Ideal Γ(S, ⊤) := ((isAffineOpen_top S).primeIdealOf ⟨s, trivial⟩).asIdeal

omit [IsAffine S] in
/-- The canonical coordinate map is the germ map followed by the spectrum comparison. -/
lemma fromSpecStalk_appTop_eq :
    (S.fromSpecStalk s).appTop =
      S.presheaf.germ ⊤ s trivial ≫ (Scheme.ΓSpecIso (S.presheaf.stalk s)).inv := by
  simp [Scheme.fromSpecStalk_appTop]

/-- The actual coordinate-ring map to the stalk spectrum is localization at the point. -/
theorem fromSpecStalk_appTop_isLocalization :
    let _ := (S.fromSpecStalk s).appTop.hom.toAlgebra
    IsLocalization (pointIdeal S s).primeCompl Γ(Spec (S.presheaf.stalk s), ⊤) := by
  let _ := TopCat.Presheaf.algebra_section_stalk S.presheaf
    (⟨s, trivial⟩ : (⊤ : S.Opens))
  have h := (isAffineOpen_top S).isLocalization_stalk ⟨s, trivial⟩
  have he := (IsLocalization.isLocalization_iff_of_ringEquiv (pointIdeal S s).primeCompl
    (Scheme.ΓSpecIso (S.presheaf.stalk s)).commRingCatIsoToRingEquiv.symm).mp h
  rw [fromSpecStalk_appTop_eq]
  exact he

/-- The local-ring spectrum maps flatly to an affine base. -/
theorem fromSpecStalk_flat : Flat (S.fromSpecStalk s) := by
  let _ := (S.fromSpecStalk s).appTop.hom.toAlgebra
  let _ := fromSpecStalk_appTop_isLocalization S s
  apply (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mpr
  exact RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat Γ(Spec (S.presheaf.stalk s), ⊤) (pointIdeal S s).primeCompl)

end FLT.Mazur.StalkBase
