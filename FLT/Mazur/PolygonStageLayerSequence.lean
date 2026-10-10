/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageFlatLayer
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The natural short exact layer sequence

The adjacent quotient of a flat truncated-stage module has the closed-fiber
quotient as its kernel. Linear maps respect the explicit last-power inclusion,
so these local sequences can be compared under actual section restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace FLT.Mazur.PolygonInfinitesimalStages

variable (R : Type*) [CommRing R] (m : ℕ)
  (M : Type*) [AddCommGroup M] [Module (Ring R (m + 1)) M]

/-- Quotient a stage module by a specified power of the actual parameter. -/
abbrev parameterQuotient (k : ℕ) :=
  M ⧸ LinearMap.range (DistribSMul.toLinearMap (Ring R (m + 1)) M
    (parameter R (m + 1) ^ k))

variable {M} {N : Type*} [AddCommGroup N] [Module (Ring R (m + 1)) N]

/-- A linear map descends to every actual parameter-power quotient. -/
def parameterQuotientMap (f : M →ₗ[Ring R (m + 1)] N) (k : ℕ) :
    parameterQuotient R m M k →ₗ[Ring R (m + 1)] parameterQuotient R m N k :=
  Submodule.mapQ _ _ f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (f.map_smul _ y).symm⟩)

/-- Descending a linear map retains its formula on section classes. -/
theorem parameterQuotientMap_mk (f : M →ₗ[Ring R (m + 1)] N) (k : ℕ) (x : M) :
    parameterQuotientMap R m f k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) := rfl

/-- Quotient maps respect composition, including the maps used for open restriction. -/
theorem parameterQuotientMap_comp {P : Type*} [AddCommGroup P]
    [Module (Ring R (m + 1)) P] (f : M →ₗ[Ring R (m + 1)] N)
    (g : N →ₗ[Ring R (m + 1)] P) (k : ℕ) :
    parameterQuotientMap R m (g.comp f) k =
      (parameterQuotientMap R m g k).comp (parameterQuotientMap R m f k) := by
  apply Submodule.linearMap_qext
  rfl

variable (M) [Module.Flat (Ring R (m + 1)) M]

/-- The actual layer complex, with the closed coefficient quotient in the first term. -/
def flatLayerSequence : ShortComplex (ModuleCat (Ring R (m + 1))) :=
  ModuleCat.shortComplexOfCompEqZero (closedLayerInclusion R m M)
    (LinearMap.range (DistribSMul.toLinearMap (Ring R (m + 1)) M
      (parameter R (m + 1) ^ (m + 1)))).mkQ
    (closedLayerInclusion_exact R m M).linearMap_comp_eq_zero

/-- No lifting assumption is needed for exactness of the flat local layer sequence. -/
theorem flatLayerSequence_shortExact : (flatLayerSequence R m M).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (closedLayerInclusion_exact R m M)
    (closedLayerInclusion_injective R m M) (Submodule.mkQ_surjective _)

variable {M} [Module.Flat (Ring R (m + 1)) N]

/-- The induced map on closed coefficient fibers. -/
def closedLayerMap (f : M →ₗ[Ring R (m + 1)] N) :
    (M ⧸ LinearMap.range (DistribSMul.toLinearMap (Ring R (m + 1)) M
      (parameter R (m + 1)))) →ₗ[Ring R (m + 1)]
    (N ⧸ LinearMap.range (DistribSMul.toLinearMap (Ring R (m + 1)) N
      (parameter R (m + 1)))) :=
  Submodule.mapQ _ _ f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (f.map_smul _ y).symm⟩)

/-- The closed-fiber inclusion commutes with every linear map of flat stage modules. -/
theorem closedLayerInclusion_natural (f : M →ₗ[Ring R (m + 1)] N) :
    f.comp (closedLayerInclusion R m M) =
      (closedLayerInclusion R m N).comp (closedLayerMap R m f) := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro y
  exact f.map_smul _ y

end FLT.Mazur.PolygonInfinitesimalStages
