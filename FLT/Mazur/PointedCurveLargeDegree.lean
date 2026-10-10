/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveLargeDegreeVanishing
public import FLT.Mazur.SectionSumFieldLength
public import FLT.Mazur.CurvePositiveDegreeAmple

/-!
# Large-degree Riemann–Roch on a pointed smooth proper integral curve

The actual rational point supplies its Cartier ideal and a line of degree
one. Positive degree proves ampleness, so the uniform vanishing theorem
requires no supplied ample line or cohomology witness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]

omit [IsIntegral X] in
/-- The line of a rational point has degree one, retaining the full section ideal. -/
theorem pointedCurve_line_degree_one (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    curveSheafDegree f
      (divisorLineBundle s.ker (smoothSectionCartier f s inferInstance inferInstance hs).1) =
        1 := by
  let _ : IsFinite (s.ker.subschemeι ≫ f) := by
    rw [← sectionImageIso_hom f s hs]
    infer_instance
  rw [divisor_degree_eq_fieldLength, divisorFieldLength_section f s hs, Nat.cast_one]

/-- A rational point on a smooth proper integral curve constructs an actual ample line. -/
theorem pointedCurve_exists_ample_line (hd : topologicalKrullDim X ≤ 1)
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    ∃ A : X.Modules, AmpleLineBundle A := by
  let hI := (smoothSectionCartier f s inferInstance inferInstance hs).1
  refine ⟨divisorLineBundle s.ker hI,
    ampleLineBundle_of_curveSheafDegree_pos f hd hI.divisorLineBundle_locallyFreeRankOne ?_⟩
  rw [pointedCurve_line_degree_one f s hs]
  decide

/-- All sufficiently large-degree lines have vanishing H¹ on a pointed smooth proper curve. -/
theorem pointedCurve_large_degree_riemannRoch (hd : topologicalKrullDim X = 1)
    (hc : HasConstantGlobalSections f)
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    ∃ d : ℤ, ∀ L : X.Modules, LocallyFreeRankOne L → d ≤ curveSheafDegree f L →
      Subsingleton (ModuleScalarH f L 1) ∧
        (Module.finrank k (ModuleScalarH f L 0) : ℤ) =
          curveSheafDegree f L + 1 - curveGenus f hd hc := by
  obtain ⟨A, hA⟩ := pointedCurve_exists_ample_line f hd.le s hs
  exact exists_degree_bound_riemannRoch f hd hc hA

end FLT.Mazur.FCurve
