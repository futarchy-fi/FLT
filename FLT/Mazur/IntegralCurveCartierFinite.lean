/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierCharts
public import FLT.Mazur.ClosedSubsets
public import FLT.Mazur.SmoothCurveDimension

/-!
# Finiteness of Cartier divisors on integral curves

A regular local equation cannot vanish on an entire reduced nonempty scheme.
On an integral Noetherian curve the resulting proper closed support is finite.
The conclusion concerns the full closed subscheme, retaining multiplicities.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- A Cartier divisor cannot be the zero ideal on a nonempty scheme. -/
theorem EffectiveCartier.ne_bot [Nonempty X] (hI : EffectiveCartier I) : I ≠ ⊥ := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hx, a, ha, hUa⟩ := hI x
  have : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  have : Nontrivial Γ(X, U) := inferInstance
  have hz : a = 0 := by
    apply Ideal.span_singleton_eq_bot.mp
    rw [← hUa, h]
    rfl
  exact ha.ne_zero hz

/-- On a reduced nonempty scheme the Cartier support is proper. -/
theorem EffectiveCartier.support_ne_top [IsReduced X] [Nonempty X]
    (hI : EffectiveCartier I) : I.support ≠ ⊤ :=
  fun h ↦ hI.ne_bot (Scheme.IdealSheafData.support_eq_top_iff.mp h)

/-- A Cartier divisor on an integral Noetherian curve has finite support. -/
theorem EffectiveCartier.finite_support [IsIntegral X] [IsNoetherian X]
    (hI : EffectiveCartier I) (hd : topologicalKrullDim X ≤ 1) :
    (I.support : Set X).Finite := by
  apply finite_of_isClosed_of_ne_univ hd I.support.isClosed
  intro h
  exact hI.support_ne_top (SetLike.coe_injective h)

/-- Finite support gives a finite full closed divisor over the ground field. -/
theorem EffectiveCartier.isFinite_of_integral_curve {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsIntegral X] (hI : EffectiveCartier I) (hd : topologicalKrullDim X ≤ 1) :
    IsFinite (I.subschemeι ≫ f) := by
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  have : Finite I.subscheme :=
    (Set.finite_range_iff I.subschemeι.isClosedEmbedding.injective).mp
      (I.range_subschemeι.symm ▸ hI.finite_support hd)
  let _ : LocallyQuasiFinite (I.subschemeι ≫ f) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ ↦ Set.toFinite _)
  exact IsFinite.of_locallyQuasiFinite _

/-- Smooth relative dimension one supplies the dimension bound for an integral curve. -/
theorem EffectiveCartier.isFinite_of_integral_smoothCurve {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 f] [QuasiCompact f]
    [IsIntegral X] (hI : EffectiveCartier I) : IsFinite (I.subschemeι ≫ f) := by
  let _ := SmoothOfRelativeDimension.smooth 1 f
  exact hI.isFinite_of_integral_curve f
    (smoothCurveDimension f inferInstance inferInstance).le

end FLT.Mazur.FCurve
