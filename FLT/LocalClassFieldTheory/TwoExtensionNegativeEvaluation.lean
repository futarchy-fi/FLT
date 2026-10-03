/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleNegativeBoundary
public import FLT.LocalClassFieldTheory.TateInvariantClass
public import FLT.LocalClassFieldTheory.TateTwoExtension
public import FLT.LocalClassFieldTheory.TwoCocycleNormSum

/-!
# Evaluating the actual two-extension in degree minus two

The two genuine connecting maps send a scalar bar generator at `g` to the
invariant class of `∑ h, c(h,g⁻¹)`. No evaluation is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (M : Rep k G) (c : cocycles₂ M) (g : G)

local notation "I" => coinducedCoefficients M
local notation "Q" => shiftedCoefficients M
local notation "b" => shiftedTwoCocycle M c

/-- The concrete primitive lifts the first negative boundary. -/
theorem twoExtension_negative_lift :
    (tateComplex.map (shiftedProjection M)).f (-1)
      ((chainsIso₀ I).inv (twoCocyclePrimitive M c g⁻¹)) =
        (chainsIso₀ Q).inv (b g⁻¹) := by
  change (chainsMap (MonoidHom.id G) (B := Q) (shiftedProjection M)).f 0 _ = _
  apply (ModuleCat.mono_iff_injective (chainsIso₀ Q).hom).mp inferInstance
  have h := congrArg (fun f => f.hom ((chainsIso₀ I).inv (twoCocyclePrimitive M c g⁻¹)))
    (chainsMap_f_0_comp_chainsIso₀ (B := Q) (MonoidHom.id G) (shiftedProjection M))
  change (chainsIso₀ Q).hom
    ((chainsMap (MonoidHom.id G) (B := Q) (shiftedProjection M)).f 0 _) =
    (shiftedProjection M).hom ((chainsIso₀ I).hom ((chainsIso₀ I).inv _)) at h
  rw [Iso.inv_hom_id_apply] at h ⊢
  exact h

/-- The norm differential of the lifted primitive is the included invariant sum. -/
theorem twoExtension_negative_d :
    (tateComplex.map (coinducedInclusion M)).f 0
        ((cochainsIso₀ M).inv (twoCocycleSum M c g⁻¹)) =
      (tateComplex I).d (-1) (-1 + 1)
        ((chainsIso₀ I).inv (twoCocyclePrimitive M c g⁻¹)) := by
  change (cochainsMap (MonoidHom.id G) (coinducedInclusion M)).f 0 _ =
    (cochainsIso₀ I).inv ((I).norm.hom ((chainsIso₀ I).hom ((chainsIso₀ I).inv _)))
  rw [Iso.inv_hom_id_apply, twoCocyclePrimitive_norm]
  apply (ModuleCat.mono_iff_injective (cochainsIso₀ I).hom).mp inferInstance
  have h := congrArg (fun f => f.hom ((cochainsIso₀ M).inv (twoCocycleSum M c g⁻¹)))
    (cochainsMap_f_0_comp_cochainsIso₀ (MonoidHom.id G) (coinducedInclusion M))
  change (cochainsIso₀ I).hom
    ((cochainsMap (MonoidHom.id G) (coinducedInclusion M)).f 0 _) =
    (coinducedInclusion M).hom ((cochainsIso₀ M).hom ((cochainsIso₀ M).inv _)) at h
  rw [Iso.inv_hom_id_apply] at h ⊢
  exact h

/-- The second negative boundary is the invariant class of the finite cocycle sum. -/
theorem twoExtension_negative_second_boundary :
    TateCohomology.δ (coinducedCoefficientSequence_shortExact M) (-1)
      (tateCocycleClass Q (-1) ((chainsIso₀ Q).inv (b g⁻¹))
        (oneCocycle_negative_cycle Q b g)) =
      tateInvariantClass M (twoCocycleSumInvariant M c g⁻¹) := by
  rw [tateInvariantClass_apply]
  exact tateConnecting_apply (coinducedCoefficientSequence_shortExact M) (-1) _
    (oneCocycle_negative_cycle Q b g) _ (twoExtension_negative_lift M c g) _
      (twoExtension_negative_d M c g)

/-- Evaluation of the constructed cup in degree minus two on a scalar bar generator. -/
theorem tateTwoExtensionMap_generator :
    tateTwoExtensionMap M c (-2) (tateScalarGenerator k G g) =
      tateInvariantClass M (twoCocycleSumInvariant M c g⁻¹) := by
  change TateCohomology.δ (coinducedCoefficientSequence_shortExact M) (-1)
    (TateCohomology.δ (oneCocycleSequence_shortExact Q b) (-2)
      (tateScalarGenerator k G g)) = _
  rw [oneCocycle_negative_boundary, twoExtension_negative_second_boundary]

end LocalClassFieldTheory
