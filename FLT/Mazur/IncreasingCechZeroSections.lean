/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechZeroRestriction
public import FLT.Mazur.IncreasingCechLocalization
public import FLT.Mazur.ChowWitnessSectionsLocalization

/-!
# Actual sections as bounded zero-cycles

Sheaf gluing and the degree-zero sorting comparison identify original global
sections with the bounded kernel. The base-ring action is retained throughout.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechScalars
open CechSheafHZero FCurve Chow

variable {X : Scheme} {ι : Type} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens)

/-- Actual full zero-cycles are the linear pairwise compatibility kernel. -/
def fullZeroChartEquiv :
    (finiteCechDifferential M U 0 1).ker ≃ₗ[Γ(X, ⊤)]
      (baseDifference M (RingHom.id _) U).ker where
  toFun x := ⟨zeroTermEquiv U (moduleAbelianSheaf M) x.val,
    (baseDifference_mem_ker M (RingHom.id _) U _).mpr
      ((d_zero_iff_compatible U (moduleAbelianSheaf M) x.val).mp x.property)⟩
  invFun x := ⟨(zeroTermEquiv U (moduleAbelianSheaf M)).symm x.val,
    (d_zero_iff_compatible U (moduleAbelianSheaf M) _).mpr (by
      rw [AddEquiv.apply_symm_apply]
      exact (baseDifference_mem_ker M (RingHom.id _) U _).mp x.property)⟩
  left_inv x := Subtype.ext ((zeroTermEquiv U (moduleAbelianSheaf M)).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((zeroTermEquiv U (moduleAbelianSheaf M)).apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add (zeroTermEquiv U (moduleAbelianSheaf M)) x.val y.val)
  map_smul' r x := by
    apply Subtype.ext
    funext i
    exact zeroTermEquiv_naturality U (moduleMultiply M r) x.val i

/-- The bounded zero-cycle kernel is obtained from actual sheaf gluing. -/
def sectionsZeroKernelEquiv (hCover : iSup U = ⊤) :
    baseSections M (RingHom.id _) ⊤ ≃ₗ[Γ(X, ⊤)] (linearDifferential M U 0).ker :=
  (baseSectionsEqualizer M (RingHom.id _) U hCover).trans
    ((fullZeroChartEquiv M U).symm.trans (zeroKernelRestrictionEquiv M U))

variable {R : Type} [CommRing R] (ρ : R →+* Γ(X, ⊤))

/-- The actual global sections to bounded-kernel comparison over the original base. -/
def baseSectionsZeroKernelEquiv (hCover : iSup U = ⊤) :
    baseSections M ρ ⊤ ≃ₗ[R] (baseD M U ρ 0).ker :=
  { (sectionsZeroKernelEquiv M U hCover).toAddEquiv with
    map_smul' := fun r x ↦ (sectionsZeroKernelEquiv M U hCover).map_smul (ρ r) x }

/-- Localized original global sections identify with the actual localized degree-zero kernel. -/
def localizedSectionsZeroKernelEquiv (hCover : iSup U = ⊤) (S : Submonoid R) :
    LocalizedModule S (baseSections M ρ ⊤) ≃ₗ[Localization S] (localD M U ρ S 0).ker :=
  (IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S _)
    (LocalizedModule.mkLinearMap S _) (Localization S)
      (baseSectionsZeroKernelEquiv M U ρ hCover)).trans
    (LocalizedKernelComparison.kernelEquiv S (baseD M U ρ 0))

end FLT.Mazur.IncreasingCechScalars
