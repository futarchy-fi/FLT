/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementExactPowers
public import FLT.Mazur.PolygonCompletePointLeadingProducts

/-!
# Exact weighted orders on every original field square

The original pole-two and pole-three functions have monomials of exact
order 2a+3b. The argument uses the retained rational Cartier marking, with
no integrality assumption on the ambient curve and no replacement functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- Every nonconstant original weighted monomial excludes the preceding pole bound. -/
theorem completeCartesianPoint_monomial_not_mem (i : Fin n) (a b : ℕ)
    (hab : 0 < a + b) :
    (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide)) ^ a *
      (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)) ^ b ∉
        divisorPoleFunctions (completeCartesianMarking_relativeCartier K n h s p q hs i).1
          (2 * a + 3 * b - 1) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let e := sectionImageIso q (completeCartesianMarking K n h s p q hs i)
    (completeCartesianMarking_snd K n h s p q hs i)
  let _ : IsIntegral (completeCartesianMarking K n h s p q hs i).ker.subscheme :=
    IsIntegral.of_isIso e.inv
  let _ : Subsingleton (completeCartesianMarking K n h s p q hs i).ker.subscheme :=
    (Scheme.homeoOfIso e).injective.subsingleton
  exact divisorPoleFunctions_monomial_not_mem q
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1 2 3 (by decide) (by decide)
    (completeCartesianPointNewFunction_mem K n h L s p q hs i 1 (by decide))
    (completeCartesianPointNewFunction_mem K n h L s p q hs i 2 (by decide))
    (completeCartesianPointNewFunction_not_mem K n h L s p q hs i 1 (by decide))
    (completeCartesianPointNewFunction_not_mem K n h L s p q hs i 2 (by decide)) a b hab

/-- An original nonconstant monomial has no strictly smaller pole bound. -/
theorem completeCartesianPoint_monomial_not_mem_lt (i : Fin n) (a b d : ℕ)
    (hd : d < 2 * a + 3 * b) :
    (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide)) ^ a *
      (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)) ^ b ∉
        divisorPoleFunctions (completeCartesianMarking_relativeCartier K n h s p q hs i).1 d := by
  intro hm
  apply completeCartesianPoint_monomial_not_mem K n h L s p q hs i a b (by omega)
  exact divisorPoleFunctions_mono _ (by omega) hm

/-- These actual monomials are nonzero regular functions on the retained complement. -/
theorem completeCartesianPoint_monomial_ne_zero (i : Fin n) (a b : ℕ)
    (hab : 0 < a + b) :
    (completeCartesianPointNewFunction K n h L s p q hs i 1 (by decide)) ^ a *
      (completeCartesianPointNewFunction K n h L s p q hs i 2 (by decide)) ^ b ≠ 0 := by
  intro he
  apply completeCartesianPoint_monomial_not_mem K n h L s p q hs i a b hab
  rw [he]
  exact (divisorPoleFunctions _ _).zero_mem

end FLT.Mazur.PolygonInfinitesimalStages
