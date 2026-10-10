/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCurveLargeDegree
public import FLT.Mazur.CurveUniformFieldDegreeBound
public import FLT.Mazur.SmoothDimensionBound

/-!
# Uniform Riemann–Roch for pointed smooth curves after field extension

The point constructs the ample line and smoothness supplies each curve's
dimension bound. A single integer works over all extension fields where the
curve is integral, for every new line bundle, whether or not it descends.
The output includes an actual nonzero section and the exact section dimension.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]

/-- A pointed smooth integral proper curve has a field-independent Riemann–Roch bound. -/
theorem pointedCurve_uniform_field_riemannRoch (hd : topologicalKrullDim X = 1)
    (hc : HasConstantGlobalSections f)
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    ∃ d : ℤ, ∀ (K : Type) [Field K] (P : Scheme) [IsIntegral P]
      (p : P ⟶ X) (q : P ⟶ Spec (.of K)) (g : Spec (.of K) ⟶ Spec (.of k)),
      IsPullback p q f g → ∀ L : P.Modules, LocallyFreeRankOne L →
      d ≤ curveSheafDegree q L →
        Subsingleton (ModuleScalarH q L 1) ∧
          (Module.finrank K (ModuleScalarH q L 0) : ℤ) =
            curveSheafDegree q L + 1 - curveGenus f hd hc ∧
          ∃ t : Γ(L, ⊤), t ≠ 0 := by
  obtain ⟨A, hA⟩ := pointedCurve_exists_ample_line f hd.le s hs
  obtain ⟨d, hbound⟩ := exists_uniform_field_degree_bound f hd hc hA
  refine ⟨max d (curveGenus f hd hc), ?_⟩
  intro K _ P _ p q g h L hL hdeg
  have : SmoothOfRelativeDimension 1 q := MorphismProperty.of_isPullback h inferInstance
  have hz := hbound K P p q g h (topologicalKrullDim_le_one_of_smooth q)
    L hL ((le_max_left _ _).trans hdeg)
  have he := curve_field_h0_eq_of_h1_vanishing f hd hc h L
  refine ⟨hz, he, exists_nonzero_section_of_h0_pos q L ?_⟩
  have hg := (le_max_right d (curveGenus f hd hc : ℤ)).trans hdeg
  omega

end FLT.Mazur.FCurve
