/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveLineHigherVanishing
public import FLT.Mazur.PointedCurveUniformRiemannRoch

/-!
# Uniform positive acyclicity of large-degree lines

The degree bound for H¹ combines with dimension-one higher vanishing. One
integer therefore kills every positive cohomology group of every sufficiently
large-degree line over every integral field extension of the pointed curve.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]

/-- One degree bound gives all positive vanishing on every integral field extension. -/
theorem pointedCurve_uniform_field_acyclicity (hd : topologicalKrullDim X = 1)
    (hc : HasConstantGlobalSections f)
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    ∃ d : ℤ, ∀ (K : Type) [Field K] (P : Scheme) [IsIntegral P]
      (p : P ⟶ X) (q : P ⟶ Spec (.of K)) (g : Spec (.of K) ⟶ Spec (.of k)),
      IsPullback p q f g → ∀ L : P.Modules, LocallyFreeRankOne L →
      d ≤ curveSheafDegree q L → ∀ n, Subsingleton (ModuleH L (n + 1)) := by
  obtain ⟨B, hB⟩ := pointedCurve_exists_ample_line f hd.le s hs
  obtain ⟨d, hbound⟩ := exists_uniform_field_degree_bound f hd hc hB
  refine ⟨d, ?_⟩
  intro K _ P _ p q g h L hL hdeg n
  let _ : IsProper q := MorphismProperty.of_isPullback h inferInstance
  let _ : SmoothOfRelativeDimension 1 q := MorphismProperty.of_isPullback h inferInstance
  have hdP := topologicalKrullDim_le_one_of_smooth q
  cases n with
  | zero => exact hbound K P p q g h hdP L hL hdeg
  | succ n =>
    let _ : IsAffineHom p := MorphismProperty.of_isPullback h.flip inferInstance
    exact curve_line_higher_vanishing q hdP (hB.pullback_affine p) hL n

end FLT.Mazur.FCurve
