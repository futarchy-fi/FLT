/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCohomologyImage

/-!
# The affine degree-zero cohomology image filtration

On a spectrum, the actual image filtration in degree zero is exactly the
ordinary adic filtration. The comparison uses genuine global sections and
the original image inclusions, with their coordinate-ring scalar action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.IdealAdicQuotient

universe u

namespace FLT.Mazur.AffineAdicCohomology

variable {R : CommRingCat.{u}}

/-- Degree-zero cohomology on a spectrum retains the original coordinate-ring action. -/
def h0Equiv (M : (Spec R).Modules) :
    ModuleRingH (Scheme.ΓSpecIso R).inv.hom M 0 ≃ₗ[R] moduleSpecΓFunctor.obj M where
  toAddEquiv := (moduleH0Equiv M).toAddEquiv
  map_smul' r x := by
    change ModuleH M 0 at x
    change moduleH0Equiv M ((Scheme.ΓSpecIso R).inv r • x) =
      r • (show Γ(M, ⊤) from moduleH0Equiv M x)
    rw [(moduleH0Equiv M).map_smul, smul_Spec_def,
      show (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    rfl

/-- The degree-zero identification commutes with the actual section map. -/
lemma h0Equiv_naturality {M N : (Spec R).Modules} (g : M ⟶ N)
    (x : ModuleRingH (Scheme.ΓSpecIso R).inv.hom M 0) :
    h0Equiv N (moduleHMap g 0 x) = (moduleSpecΓFunctor.map g).hom (h0Equiv M x) :=
  moduleH0Equiv_naturality g x

variable [IsNoetherianRing R] (I : (Spec R).IdealSheafData)
  (M : (Spec R).Modules) [M.IsFinitePresentation]

/-- The actual degree-zero image maps to the ordinary ideal-power multiple of sections. -/
lemma image_map_h0Equiv (n : ℕ) :
    (cohomologyImage (Scheme.ΓSpecIso R).inv.hom I M 0 n).map (h0Equiv M).toLinearMap =
      (specIdeal I) ^ n • (⊤ : Submodule R (moduleSpecΓFunctor.obj M)) := by
  rw [← spec_power_range I n M]
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨h0Equiv (power I n M) z, (h0Equiv_naturality (inclusion (I ^ n) M) z).symm⟩
  · rintro ⟨z, rfl⟩
    let y := (h0Equiv (power I n M)).symm z
    refine ⟨moduleHMap (inclusion (I ^ n) M) 0 y, ⟨y, rfl⟩, ?_⟩
    change h0Equiv M (moduleHMap (inclusion (I ^ n) M) 0 y) = _
    rw [h0Equiv_naturality]
    exact congrArg (moduleSpecΓFunctor.map (inclusion (I ^ n) M)).hom
      ((h0Equiv (power I n M)).apply_symm_apply z)

/-- On an affine scheme the two degree-zero filtrations coincide at every exponent. -/
theorem image_eq_adic (n : ℕ) :
    cohomologyImage (Scheme.ΓSpecIso R).inv.hom I M 0 n =
      (specIdeal I) ^ n •
        (⊤ : Submodule R (ModuleRingH (Scheme.ΓSpecIso R).inv.hom M 0)) := by
  apply Submodule.map_injective_of_injective (h0Equiv M).injective
  rw [image_map_h0Equiv, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (h0Equiv M).surjective]

end FLT.Mazur.AffineAdicCohomology
