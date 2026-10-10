/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveRiemannRochEuler
public import FLT.Mazur.LineSectionCohomologySurjection
public import FLT.Mazur.CurvePicardDegree
public import FLT.Mazur.AmpleCoherentVanishing

/-!
# Uniform vanishing in sufficiently large line-bundle degree

Choose an acyclic power A of an ample line. Riemann–Roch gives a nonzero
section of A⁻¹ ⊗ L whenever deg(L) ≥ deg(A) + g. Multiplication by that
section makes H¹(L) a quotient of H¹(A), proving vanishing uniformly over
all line bundles of sufficiently large degree. No dualizing sheaf or
optimal bound 2g − 2 is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleSheafTensorAssociator ModuleLineBundleTensorPullback

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f]
  (hd : topologicalKrullDim X = 1) (hc : HasConstantGlobalSections f)

/-- An acyclic line supplies a degree bound for H¹ vanishing of every line. -/
theorem curve_h1_vanishing_of_acyclic_line {A L : X.Modules}
    (hA : LocallyFreeRankOne A) (hL : LocallyFreeRankOne L)
    [Subsingleton (ModuleScalarH f A 1)]
    (hdeg : curveSheafDegree f A + curveGenus f hd hc ≤ curveSheafDegree f L) :
    Subsingleton (ModuleScalarH f L 1) := by
  have hdual : curveSheafDegree f (moduleSheafDual A) = -curveSheafDegree f A :=
    SchemePicard.degree_inv f hd.le (SchemePicard.mk A hA)
  have hN := hA.dual.tensor hL
  have hdegree : (curveGenus f hd hc : ℤ) ≤
      curveSheafDegree f (tensor (moduleSheafDual A) L) := by
    rw [curveSheafDegree_line_tensor f hd.le hL hA.dual, hdual]
    omega
  obtain ⟨s, hs⟩ := exists_nonzero_section_of_degree_ge_genus f hd hc _ hdegree
  have hz := LineSectionTwistSystem.tensor_cohomology_vanishing_of_section
    f hd.le hA hN s hs 1 (by decide)
  let e : tensor A (tensor (moduleSheafDual A) L) ≅ L :=
    (associator A (moduleSheafDual A) L).symm ≪≫
      congr (comm A (moduleSheafDual A) ≪≫ lineSheafDualEvaluationIso hA) (Iso.refl L) ≪≫
        leftUnitor L
  let c : ModuleScalarH f (tensor A (tensor (moduleSheafDual A) L)) 1 ≃ₗ[k]
      ModuleScalarH f L 1 := ((moduleScalarHFunctor f 1).mapIso e).toLinearEquiv
  exact c.symm.injective.subsingleton

omit [IsIntegral X] in
/-- Proper Serre vanishing constructs an actual acyclic line from any ample line. -/
theorem exists_acyclic_line_of_ample {B : X.Modules} (hB : AmpleLineBundle B) :
    ∃ A : X.Modules, LocallyFreeRankOne A ∧ Subsingleton (ModuleScalarH f A 1) := by
  have := structureModule_locallyFreeRankOne.isFinitePresentation (X := X)
  obtain ⟨n, hn⟩ := hB.coherent_vanishing f (structureModule X)
  have hz := hn n le_rfl 0
  let e := leftUnitor (tensorPower B n)
  refine ⟨tensorPower B n, hB.2.1.tensorPower n, ?_⟩
  exact @moduleH_subsingleton_of_iso X _ _ e.symm 1 hz

include hd hc in
/-- One integer bounds H¹ vanishing for all sufficiently large-degree line bundles. -/
theorem exists_degree_bound_h1_vanishing {B : X.Modules} (hB : AmpleLineBundle B) :
    ∃ d : ℤ, ∀ L : X.Modules, LocallyFreeRankOne L → d ≤ curveSheafDegree f L →
      Subsingleton (ModuleScalarH f L 1) := by
  obtain ⟨A, hA, hz⟩ := exists_acyclic_line_of_ample f hB
  exact ⟨curveSheafDegree f A + curveGenus f hd hc, fun L hL hdeg ↦
    curve_h1_vanishing_of_acyclic_line f hd hc hA hL hdeg⟩

/-- Large degree gives both H¹ vanishing and the exact Riemann–Roch section dimension. -/
theorem exists_degree_bound_riemannRoch {B : X.Modules} (hB : AmpleLineBundle B) :
    ∃ d : ℤ, ∀ L : X.Modules, LocallyFreeRankOne L → d ≤ curveSheafDegree f L →
      Subsingleton (ModuleScalarH f L 1) ∧
        (Module.finrank k (ModuleScalarH f L 0) : ℤ) =
          curveSheafDegree f L + 1 - curveGenus f hd hc := by
  obtain ⟨d, hd'⟩ := exists_degree_bound_h1_vanishing f hd hc hB
  refine ⟨d, fun L hL hdeg ↦ ?_⟩
  have hz := hd' L hL hdeg
  exact ⟨hz, curve_h0_eq_of_h1_vanishing f hd hc L⟩

end FLT.Mazur.FCurve
