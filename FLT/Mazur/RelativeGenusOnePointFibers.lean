/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePointGeometric
public import FLT.Mazur.ProperLineGeometricFieldTests

/-!
# Point-power cohomology on all field fibers of a genus-one family

Algebraic closure detects vanishing and preserves the section dimension.
The conclusions hold on arbitrary specified cartesian field fibers, retaining
the original point-power coefficient and the original field action.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  {k : Type} [Field k] (g : Spec (.of k) ⟶ S)

include hg

/-- Positive point powers are acyclic on every actual field fiber. -/
theorem relative_pointPower_field_acyclic (m : ℕ) (hm : 0 < m) (n : ℕ) :
    Subsingleton (ModuleH ((Scheme.Modules.pullback (pullback.fst G.hom g)).obj
      (tensorPower (divisorLineBundle s.left.ker hI) m)) (n + 1)) :=
  properLine_field_vanishing_of_geometric G.hom _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m) (n + 1)
    (fun _ _ _ b ↦ relative_pointPower_geometric_acyclic G hg s hI b m hm n) g

/-- The dimension of sections over each field equals the positive pole bound. -/
theorem relative_pointPower_field_h0 (m : ℕ) (hm : 0 < m) :
    Module.finrank k (ModuleScalarH (pullback.snd G.hom g)
      ((Scheme.Modules.pullback (pullback.fst G.hom g)).obj
        (tensorPower (divisorLineBundle s.left.ker hI) m)) 0) = m :=
  properLine_field_finrank_of_geometric G.hom _
    (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m) 0 m
    (fun _ _ _ b ↦ relative_pointPower_geometric_h0 G hg s hI b m hm) g

/-- A specified cartesian fiber retains the same actual acyclic coefficient. -/
theorem relative_pointPower_cartesian_acyclic {P : Scheme}
    {p : P ⟶ G.left} {q : P ⟶ Spec (.of k)} (h : IsPullback p q G.hom g)
    (m : ℕ) (hm : 0 < m) (n : ℕ) :
    Subsingleton (ModuleH ((Scheme.Modules.pullback p).obj
      (tensorPower (divisorLineBundle s.left.ker hI) m)) (n + 1)) :=
  (cartesianLine_vanishing_iff h _ (n + 1)).mp
    (relative_pointPower_field_acyclic G hg s hI g m hm n)

/-- The section count is independent of the chosen cartesian fiber presentation. -/
theorem relative_pointPower_cartesian_h0 {P : Scheme}
    {p : P ⟶ G.left} {q : P ⟶ Spec (.of k)} (h : IsPullback p q G.hom g)
    (m : ℕ) (hm : 0 < m) :
    Module.finrank k (ModuleScalarH q ((Scheme.Modules.pullback p).obj
      (tensorPower (divisorLineBundle s.left.ker hI) m)) 0) = m :=
  (cartesianLine_finrank h _ 0).trans (relative_pointPower_field_h0 G hg s hI g m hm)

end FLT.Mazur.FCurve
