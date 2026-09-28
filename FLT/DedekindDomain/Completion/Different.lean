/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.DedekindDomain.Completion.TraceDual
public import FLT.DedekindDomain.Completion.IdealOrder

/-!
# The different ideal under completion

The global different extends to the different of each completed extension.
The proof extends the inverse trace-dual fractional ideal.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors
open Module Algebra

/-- Extension of fractional ideals is the span of the field image whenever
the scalar towers commute; the extension of rings need not be integral. -/
theorem FractionalIdeal.coe_extendedHom_eq_span_of_tower
    {A K : Type*} (L B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsTorsionFree A B] [Field K] [Field L] [Algebra A K] [Algebra B L]
    [IsFractionRing A K] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L] (I : FractionalIdeal A⁰ K) :
    (FractionalIdeal.extendedHom L B I : Submodule B L) =
      Submodule.span B (algebraMap K L '' (I : Set K)) := by
  rw [FractionalIdeal.extendedHom, FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.coe_extended_eq_span]
  congr 2
  apply congrArg (fun f : K →+* L ↦ (f : K → L))
  apply IsLocalization.map_unique
  intro x
  exact (IsScalarTower.algebraMap_apply A K L x).symm.trans
    (IsScalarTower.algebraMap_apply A B L x)

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace IsDedekindDomain.HeightOneSpectrum

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]
  [FiniteDimensional K L] [Module.Finite A B] [Algebra.IsSeparable K L]
  [IsTorsionFree A B] (v : HeightOneSpectrum A)

set_option backward.isDefEq.respectTransparency false in
/-- The different of an extension with an integral basis commutes with
completion at each prime where the completed field extension is separable. -/
theorem map_differentIdeal_completion
    {ι : Type*} [Finite ι] (b : Basis ι K L)
    (hb : (1 : Submodule B L).restrictScalars A = Submodule.span A (Set.range b))
    (w : v.Extension B) [Algebra.IsSeparable (v.adicCompletion K) (w.1.adicCompletion L)]
    [IsTorsionFree (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)] :
    (differentIdeal A B).map (algebraMap B (w.1.adicCompletionIntegers L)) =
      differentIdeal (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) := by
  let : IsScalarTower (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
      (w.1.adicCompletion L) := .of_algebraMap_eq fun _ ↦ rfl
  have hd := traceDual_completion_eq_span A K L B v b hb w
  have hs : Submodule.traceDual (v.adicCompletionIntegers K) (v.adicCompletion K)
      (1 : Submodule (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) =
      Submodule.span (w.1.adicCompletionIntegers L)
        (algebraMap L (w.1.adicCompletion L) ''
          (Submodule.traceDual A K (1 : Submodule B L) : Set L)) := by
    have hh := congrArg
      (fun N : Submodule (v.adicCompletionIntegers K) (w.1.adicCompletion L) ↦
        Submodule.span (w.1.adicCompletionIntegers L) (N : Set (w.1.adicCompletion L))) hd
    simpa only [Submodule.coe_restrictScalars, Submodule.span_eq,
      Submodule.span_span_of_tower] using hh
  apply (FractionalIdeal.coeIdeal_inj (K := w.1.adicCompletion L)).mp
  rw [← FractionalIdeal.extendedHom_coeIdeal_eq_map (K := L),
    coeIdeal_differentIdeal A K L B, map_inv₀,
    coeIdeal_differentIdeal (v.adicCompletionIntegers K) (v.adicCompletion K)
      (w.1.adicCompletion L) (w.1.adicCompletionIntegers L)]
  congr 1
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [FractionalIdeal.coe_extendedHom_eq_span_of_tower, FractionalIdeal.coe_dual_one]
  change Submodule.span (w.1.adicCompletionIntegers L)
    (algebraMap L (w.1.adicCompletion L) ''
      ((FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) : Submodule B L) : Set L)) = _
  rw [FractionalIdeal.coe_dual_one]
  exact hs.symm

end IsDedekindDomain.HeightOneSpectrum
