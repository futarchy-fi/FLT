/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedProjChart

/-!
# Intrinsic equations for retained homogeneous fractions

The retained fraction evaluation solves the scalar equation in the original
pulled-back tensor power. This equation does not depend on line coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules HomogeneousLocalization

namespace FLT.Mazur.SectionRetainedFractionEquation

open FCurve ModuleLineBundleTensorPullback SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] ModuleSheafTensor.tensor

variable {X Y : Scheme} (p : Y ⟶ X) (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (e : (pullback p).obj L ≅ structureModule Y)
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

/-- A retained fraction solves the original numerator-denominator equation after pullback. -/
theorem evaluation_mk (f : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (SectionRetainedProjChart.ringHom p L e q f))
    (c : NumDenSameDeg (RetainedSubringGrading.grade (grade L ⊤) q) (Submonoid.powers f))
    {d : ℕ} (hc : q * c.deg = d)
    (s t : Γ(tensorPower L d, ⊤))
    (hs : of L ⊤ d s = c.den.val.val)
    (ht : of L ⊤ d t = c.num.val.val) :
    (show Γ(Y, ⊤) from GradedProjUnitChart.evaluation
      (RetainedSubringGrading.grade (grade L ⊤) q)
      (SectionRetainedProjChart.ringHom p L e q) f hf (HomogeneousLocalization.mk c)) •
        pullGlobal p (tensorPower L d) s =
        pullGlobal p (tensorPower L d) t := by
  subst d
  rw [SectionRetainedProjChart.evaluation_eq]
  exact SectionGradedProjChart.evaluation_mk_pullGlobal p L e f.val hf
    (HomogeneousLocalizationRegradedMap.fraction _ _
      (RetainedSubringGrading.ring (grade L ⊤) q).subtype (q * ·)
      (fun _ _ ha ↦ ha) (RetainedSubringLocalization.powers_le (grade L ⊤) q f) c)
    s t hs ht

end FLT.Mazur.SectionRetainedFractionEquation
