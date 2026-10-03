/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleExtension
public import FLT.LocalClassFieldTheory.TateScalarGenerator

/-!
# The first boundary on scalar bar generators

Lifting the scalar single chain to `(0,1)` in the twisted extension gives
`b(g⁻¹)` under the chain differential. This records the inverse convention
at the negative Tate degrees explicitly.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (Q : Rep k G) (b : cocycles₁ Q) (g : G)

local notation "X" => oneCocycleExtension Q b
local notation "T" => Rep.trivial k G k

/-- The single chain with coefficient `(0,1)` lifts the scalar bar generator. -/
theorem oneCocycle_negative_lift :
    (tateComplex.map (oneCocycleProjection Q b)).f (-2)
      ((chainsIso₁ X).inv (Finsupp.single g (0, (1 : k)))) =
        (chainsIso₁ T).inv (Finsupp.single g (1 : k)) := by
  change (chainsMap (MonoidHom.id G) (B := T) (oneCocycleProjection Q b)).f 1 _ = _
  apply (ModuleCat.mono_iff_injective (chainsIso₁ T).hom).mp inferInstance
  have h := congrArg (fun f => f.hom
    ((chainsIso₁ X).inv (Finsupp.single g (0, (1 : k)))))
      (chainsMap_f_1_comp_chainsIso₁ (B := T) (MonoidHom.id G) (oneCocycleProjection Q b))
  change (chainsIso₁ T).hom ((chainsMap _ _).f 1 _) =
    chainsMap₁ (MonoidHom.id G) (B := T) (oneCocycleProjection Q b)
      ((chainsIso₁ X).hom ((chainsIso₁ X).inv _)) at h
  rw [Iso.inv_hom_id_apply] at h ⊢
  exact h.trans (by simp [chainsMap₁, oneCocycleProjection]; rfl)

/-- Differentiating the lifted chain gives the shifted cocycle at the inverse element. -/
theorem oneCocycle_negative_d :
    (tateComplex.map (oneCocycleInclusion Q b)).f (-1)
        ((chainsIso₀ Q).inv (b g⁻¹)) =
      (tateComplex X).d (-2) (-2 + 1)
        ((chainsIso₁ X).inv (Finsupp.single g (0, (1 : k)))) := by
  change (chainsMap (MonoidHom.id G) (B := X) (oneCocycleInclusion Q b)).f 0 _ =
    (inhomogeneousChains X).d 1 0 _
  apply (ModuleCat.mono_iff_injective (chainsIso₀ X).hom).mp inferInstance
  have hl := congrArg (fun f => f.hom ((chainsIso₀ Q).inv (b g⁻¹)))
    (chainsMap_f_0_comp_chainsIso₀ (B := X) (MonoidHom.id G) (oneCocycleInclusion Q b))
  have hr := congrArg (fun f => f.hom (Finsupp.single g (0, (1 : k))))
    (eq_d₁₀_comp_inv X)
  change (inhomogeneousChains X).d 1 0
    ((chainsIso₁ X).inv (Finsupp.single g (0, (1 : k)))) =
      (chainsIso₀ X).inv (d₁₀ X (Finsupp.single g (0, (1 : k)))) at hr
  rw [hr]
  rw [Iso.inv_hom_id_apply]
  change (chainsIso₀ X).hom
    ((chainsMap (MonoidHom.id G) (B := X) (oneCocycleInclusion Q b)).f 0 _) =
    (oneCocycleInclusion Q b).hom ((chainsIso₀ Q).hom ((chainsIso₀ Q).inv _)) at hl
  rw [Iso.inv_hom_id_apply] at hl
  rw [hl, d₁₀_single]
  change (b g⁻¹, 0) = (Q.ρ g⁻¹ 0 + (1 : k) • b g⁻¹, (1 : k)) - (0, 1)
  simp

/-- The inverse-element cocycle value is closed at the norm splice. -/
theorem oneCocycle_negative_cycle :
    (tateComplex Q).d (-1) (-1 + 1) ((chainsIso₀ Q).inv (b g⁻¹)) = 0 :=
  tateConnecting_cycle (oneCocycleSequence_shortExact Q b) (-2)
    ((chainsIso₁ X).inv (Finsupp.single g (0, (1 : k))))
    ((chainsIso₀ Q).inv (b g⁻¹)) (oneCocycle_negative_d Q b g)

/-- Evaluation of the genuine first Tate boundary on a scalar generator. -/
theorem oneCocycle_negative_boundary :
    TateCohomology.δ (oneCocycleSequence_shortExact Q b) (-2)
      (tateScalarGenerator k G g) =
        tateCocycleClass Q (-1) ((chainsIso₀ Q).inv (b g⁻¹))
          (oneCocycle_negative_cycle Q b g) :=
  tateConnecting_apply (oneCocycleSequence_shortExact Q b) (-2) _
    (tateScalarGenerator_cycle k G g) _ (oneCocycle_negative_lift Q b g) _
      (oneCocycle_negative_d Q b g)

end LocalClassFieldTheory
