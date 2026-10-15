/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.FlatScalarExactness
public import FLT.Mazur.PolygonArithmeticParameterAnnihilator
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exact arithmetic layers of flat modules

Multiplication by the last parameter power embeds the closed coefficient
quotient as the kernel of adjacent reduction. The maps are explicit and
natural in linear maps, ready to apply to sections on affine polygon charts.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace FLT.Mazur.PolygonArithmeticStages
variable (A : Type*) [CommRing A] [IsDomain A] (π : A) (hπ : π ≠ 0) (m : ℕ)
  (M : Type*) [AddCommGroup M] [Module (Quotient A π (m + 1)) M]
  [Module.Flat (Quotient A π (m + 1)) M]

include hπ in
/-- Flatness transports the actual last-power annihilator identity to sections. -/
theorem flat_last_smul_eq_zero_iff (x : M) :
    parameter A π (m + 1) ^ (m + 1) • x = 0 ↔
      ∃ y, parameter A π (m + 1) • y = x :=
  FlatScalarExactness.smul_eq_zero_iff M _ _
    (parameter_last_mul_eq_zero_iff A π hπ m) x

/-- The original closed coefficient quotient is exactly the last-power submodule. -/
def closedLayerEquiv :
    (M ⧸ LinearMap.range (DistribSMul.toLinearMap (Quotient A π (m + 1)) M
      (parameter A π (m + 1)))) ≃ₗ[Quotient A π (m + 1)]
    LinearMap.range (DistribSMul.toLinearMap (Quotient A π (m + 1)) M
      (parameter A π (m + 1) ^ (m + 1))) :=
  FlatScalarExactness.quotientEquivRange M _ _ (parameter_last_mul_eq_zero_iff A π hπ m)

/-- The arithmetic closed layer embeds by the actual last parameter power. -/
def closedLayerInclusion :
    (M ⧸ LinearMap.range (DistribSMul.toLinearMap (Quotient A π (m + 1)) M
      (parameter A π (m + 1)))) →ₗ[Quotient A π (m + 1)] M :=
  (LinearMap.range (DistribSMul.toLinearMap (Quotient A π (m + 1)) M
    (parameter A π (m + 1) ^ (m + 1)))).subtype.comp
      (closedLayerEquiv A π hπ m M).toLinearMap

/-- The layer map retains the expected formula on every original section class. -/
theorem closedLayerInclusion_mk (x : M) :
    closedLayerInclusion A π hπ m M (Submodule.Quotient.mk x) =
      parameter A π (m + 1) ^ (m + 1) • x := rfl

/-- The actual closed-layer inclusion is injective, by flatness. -/
theorem closedLayerInclusion_injective :
    Function.Injective (closedLayerInclusion A π hπ m M) :=
  Subtype.val_injective.comp (closedLayerEquiv A π hπ m M).injective

/-- Its image is precisely the kernel of the actual adjacent module quotient. -/
theorem closedLayerInclusion_exact :
    Function.Exact (closedLayerInclusion A π hπ m M)
      (LinearMap.range (DistribSMul.toLinearMap (Quotient A π (m + 1)) M
        (parameter A π (m + 1) ^ (m + 1)))).mkQ := by
  intro x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    exact ⟨(closedLayerEquiv A π hπ m M).symm ⟨x, hx⟩,
      congrArg Subtype.val ((closedLayerEquiv A π hπ m M).apply_symm_apply ⟨x, hx⟩)⟩
  · rintro ⟨y, rfl⟩
    exact (closedLayerEquiv A π hπ m M y).property

/-- The closed-layer and adjacent-reduction maps form the actual arithmetic complex. -/
def flatLayerSequence : ShortComplex (ModuleCat (Quotient A π (m + 1))) :=
  ModuleCat.shortComplexOfCompEqZero (closedLayerInclusion A π hπ m M)
    (LinearMap.range (DistribSMul.toLinearMap (Quotient A π (m + 1)) M
      (parameter A π (m + 1) ^ (m + 1)))).mkQ
    (closedLayerInclusion_exact A π hπ m M).linearMap_comp_eq_zero

/-- The arithmetic layer complex is short exact without assuming section lifting. -/
theorem flatLayerSequence_shortExact : (flatLayerSequence A π hπ m M).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (closedLayerInclusion_exact A π hπ m M)
    (closedLayerInclusion_injective A π hπ m M) (Submodule.mkQ_surjective _)

variable {M} {N : Type*} [AddCommGroup N] [Module (Quotient A π (m + 1)) N]
  [Module.Flat (Quotient A π (m + 1)) N]

/-- Every linear map descends to the original closed coefficient quotient. -/
def closedLayerMap (f : M →ₗ[Quotient A π (m + 1)] N) :
    (M ⧸ LinearMap.range (DistribSMul.toLinearMap (Quotient A π (m + 1)) M
      (parameter A π (m + 1)))) →ₗ[Quotient A π (m + 1)]
    (N ⧸ LinearMap.range (DistribSMul.toLinearMap (Quotient A π (m + 1)) N
      (parameter A π (m + 1)))) :=
  Submodule.mapQ _ _ f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (f.map_smul _ y).symm⟩)

/-- Closed-layer inclusion commutes with actual linear restriction maps. -/
theorem closedLayerInclusion_natural (f : M →ₗ[Quotient A π (m + 1)] N) :
    f.comp (closedLayerInclusion A π hπ m M) =
      (closedLayerInclusion A π hπ m N).comp (closedLayerMap A π m f) := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro y
  exact f.map_smul _ y

end FLT.Mazur.PolygonArithmeticStages
