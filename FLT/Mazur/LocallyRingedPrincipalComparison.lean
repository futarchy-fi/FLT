/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# The canonical spectrum comparison on localized principal sections

When actual principal restriction is a localization, the canonical comparison
on that principal open is the localization equivalence itself.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.LocallyRingedPrincipalComparison
universe u
set_option backward.isDefEq.respectTransparency false
variable (X : LocallyRingedSpace.{u}) (r : X.presheaf.obj (op ⊤))

/-- The canonical principal comparison is an isomorphism when restriction is localization. -/
theorem isIso_principalComparison
    (h : let _ := (X.toToΓSpecMapBasicOpen r).hom.toAlgebra
      IsLocalization.Away r (X.presheaf.obj (op (X.toΓSpecMapBasicOpen r)))) :
    IsIso (X.toΓSpecCApp r) := by
  let _ := (X.toToΓSpecMapBasicOpen r).hom.toAlgebra
  let _ := h
  let _ := StructureSheaf.IsLocalization.to_basicOpen (X.presheaf.obj (op ⊤)) r
  let e := IsLocalization.algEquiv (Submonoid.powers r)
    ((Spec.structureSheaf (X.presheaf.obj (op ⊤))).obj.obj
      (op (PrimeSpectrum.basicOpen r)))
    (X.presheaf.obj (op (X.toΓSpecMapBasicOpen r)))
  have he : CommRingCat.ofHom e.toRingHom = X.toΓSpecCApp r := by
    apply (X.toΓSpecCApp_iff r _).mp
    ext a
    exact e.commutes a
  rw [← he]
  exact e.toRingEquiv.toCommRingCatIso.isIso_hom

/-- The actual sheaf component agrees with this principal localization isomorphism. -/
theorem isIso_principalSheafComponent
    (h : let _ := (X.toToΓSpecMapBasicOpen r).hom.toAlgebra
      IsLocalization.Away r (X.presheaf.obj (op (X.toΓSpecMapBasicOpen r)))) :
    IsIso (X.toΓSpecSheafedSpace.hom.c.app (op (PrimeSpectrum.basicOpen r))) := by
  rw [X.toΓSpecSheafedSpace_app_eq]
  exact isIso_principalComparison X r h

end FLT.Mazur.LocallyRingedPrincipalComparison
