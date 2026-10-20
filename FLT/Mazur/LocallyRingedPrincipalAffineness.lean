/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyRingedPrincipalComparison
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Affineness from the canonical topology and actual principal localization

A homeomorphism to the spectrum of global sections becomes a locally ringed
isomorphism when the original principal restrictions are localizations.
The sheaf comparison is the canonical map, detected on spectrum basic opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.LocallyRingedPrincipalComparison
universe u
set_option backward.isDefEq.respectTransparency false
variable (X : LocallyRingedSpace.{u})

/-- Principal localization and the original comparison topology imply actual affineness. -/
theorem isIso_toΓSpec
    (htop : IsHomeomorph X.toΓSpecBase)
    (hloc : ∀ r : X.presheaf.obj (op ⊤),
      let _ := (X.toToΓSpecMapBasicOpen r).hom.toAlgebra
      IsLocalization.Away r (X.presheaf.obj (op (X.toΓSpecMapBasicOpen r)))) :
    IsIso X.toΓSpec := by
  let φ : Spec.structureSheaf (LocallyRingedSpace.Γ.obj (op X)) ⟶
      (TopCat.Sheaf.pushforward CommRingCat X.toΓSpecBase).obj X.𝒪 :=
    ⟨X.toΓSpecSheafedSpace.hom.c⟩
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens
    (fun r => isIso_principalSheafComponent X r (hloc r))
  have : IsIso X.toΓSpecSheafedSpace.hom.c :=
    (TopCat.Sheaf.forget _ _).map_isIso φ
  have : IsIso X.toΓSpecSheafedSpace.hom.base :=
    (TopCat.isoOfHomeo (htop.homeomorph X.toΓSpecBase)).isIso_hom
  have : IsIso X.toΓSpecSheafedSpace.hom :=
    PresheafedSpace.isIso_of_components _
  have : IsIso (SheafedSpace.forgetToPresheafedSpace.map X.toΓSpecSheafedSpace) := by
    change IsIso X.toΓSpecSheafedSpace.hom
    infer_instance
  have : IsIso X.toΓSpecSheafedSpace :=
    isIso_of_reflects_iso _ SheafedSpace.forgetToPresheafedSpace
  have : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map X.toΓSpec) := by
    change IsIso X.toΓSpecSheafedSpace
    infer_instance
  exact isIso_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace

end FLT.Mazur.LocallyRingedPrincipalComparison
