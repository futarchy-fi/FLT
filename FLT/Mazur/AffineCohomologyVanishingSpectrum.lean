/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCohomologyVanishingRelExact

/-!
# Positive cohomology vanishes for quasi-coherent modules on spectra

Relative principal-cover exactness verifies the cofinal-cover criterion for
every tilde module. The canonical map from the tilde of global sections then
transports all positive-degree vanishing to quasi-coherent modules on a spectrum.
The result concerns the actual Ext-based sheaf and module cohomology groups.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace FLT.Mazur.AffineCohomologyVanishingSpectrum

variable {R : CommRingCat.{u}}
    [HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (TopCat.of (Spec R))) AddCommGrpCat.{u})]

/-- Every positive Ext-based sheaf cohomology group of an affine tilde module vanishes. -/
theorem tilde_sheafH_succ_subsingleton (M : ModuleCat.{u} R) (q : ℕ) :
    Subsingleton (Sheaf.H (FCurve.moduleAbelianSheaf (tilde M)) (q + 1)) :=
  AffineCohomologyVanishingCofinal.sheafH_succ_subsingleton _
    (AffineCohomologyVanishingRelExact.tilde_principalCoverExact M) q

/-- Quasi-coherent modules on a spectrum have zero sheaf cohomology in positive degrees. -/
theorem quasicoherent_sheafH_succ_subsingleton (M : (Spec R).Modules)
    [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (Sheaf.H (FCurve.moduleAbelianSheaf M) (q + 1)) := by
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let f : FCurve.moduleAbelianSheaf (tilde (moduleSpecΓFunctor.obj M)) ⟶
      FCurve.moduleAbelianSheaf M :=
    (SheafOfModules.toSheaf (Spec R).ringCatSheaf).map M.fromTildeΓ
  have : IsIso f := Functor.map_isIso _ _
  have := tilde_sheafH_succ_subsingleton (moduleSpecΓFunctor.obj M) q
  have hinj : Function.Injective (Sheaf.H.map (inv f) (q + 1)) := by
    intro a b h
    have he := congrArg (Sheaf.H.map f (q + 1)) h
    simpa only [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id, Sheaf.H.map_id_apply] using he
  exact hinj.subsingleton

end FLT.Mazur.AffineCohomologyVanishingSpectrum

namespace FLT.Mazur.FCurve

local instance affineSpectrumHasExt (R : CommRingCat.{u}) :
    HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (TopCat.of (Spec R))) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- Positive-degree vanishing for the module cohomology of an affine tilde module. -/
theorem tilde_moduleH_succ_subsingleton {R : CommRingCat.{u}}
    (M : ModuleCat.{u} R) (q : ℕ) : Subsingleton (ModuleH (tilde M) (q + 1)) :=
  AffineCohomologyVanishingSpectrum.tilde_sheafH_succ_subsingleton M q

/-- Every quasi-coherent module on a spectrum has zero positive-degree module cohomology. -/
theorem quasicoherent_moduleH_succ_subsingleton {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (ModuleH M (q + 1)) :=
  AffineCohomologyVanishingSpectrum.quasicoherent_sheafH_succ_subsingleton M q

end FLT.Mazur.FCurve
