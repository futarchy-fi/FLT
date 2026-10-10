/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechZeroSections
/-!
# Coordinate formulas for actual zero-cycles

The bounded sheaf-gluing equivalence uses the original restriction maps, and its
localization keeps the actual section fraction. These formulas identify the
assembled geometric comparison on pure tensors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.IncreasingCechScalars
open CechSheafHZero FCurve Chow IncreasingCechComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} {ι : Type} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens) {R : Type} [CommRing R]
  (ρ : R →+* Γ(X, ⊤)) (hCover : iSup U = ⊤)
/-- A bounded zero-cycle records the actual restriction on every increasing chart. -/
lemma baseSectionsZeroKernelEquiv_apply (s : baseSections M ρ ⊤) (a : Tuple (ι := ι) 0) :
    (baseSectionsZeroKernelEquiv M U ρ hCover s).val a =
      baseRestriction M ρ (show V U 0 a.val ≤ ⊤ from le_top) s := by
  change (termEquiv U (moduleAbelianSheaf M) 0
    ((zeroTermEquiv U (moduleAbelianSheaf M)).symm
      (fun i ↦ baseRestriction M ρ (show U i ≤ ⊤ from le_top) s))) a.val = _
  simp only [zeroTermEquiv, AddEquiv.symm_trans_apply, AddEquiv.apply_symm_apply]
  change M.presheaf.map _ (M.presheaf.map _ s) = M.presheaf.map _ s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl
/-- Localizing the actual section cycle preserves its numerator and denominator. -/
lemma localizedSectionsZeroKernelEquiv_mk (W : Submonoid R) (s : baseSections M ρ ⊤) (w : W) :
    (localizedSectionsZeroKernelEquiv M U ρ hCover W (LocalizedModule.mk s w)).val =
      LocalizedModule.mk (baseSectionsZeroKernelEquiv M U ρ hCover s).val w := by
  change (LocalizedKernelComparison.kernelEquiv W (baseD M U ρ 0)
    (IsLocalizedModule.mapEquiv W _ _ (Localization W)
      (baseSectionsZeroKernelEquiv M U ρ hCover) (LocalizedModule.mk s w))).val = _
  rw [show IsLocalizedModule.mapEquiv W _ _ (Localization W)
      (baseSectionsZeroKernelEquiv M U ρ hCover) (LocalizedModule.mk s w) =
        LocalizedModule.mk (baseSectionsZeroKernelEquiv M U ρ hCover s) w from
    LocalizedModule.map_mk W (baseSectionsZeroKernelEquiv M U ρ hCover).toLinearMap s w]
  exact LocalizedKernelComparison.kernelEquiv_mk W _ _ w
end FLT.Mazur.IncreasingCechScalars
