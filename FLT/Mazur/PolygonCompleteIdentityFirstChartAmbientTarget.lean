/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartResidualPresentation
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphErrors

/-!
# Original target functions and their node values in the ambient presentation

The unchanged target coordinate map reduces to reciprocal scaling of the
original source. This equality is only a node-reduction statement.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstGraphReduction completeIdentityFirstGraphSource
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "A" => Ring K 1
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "B" => ChartRing (t)
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "c" => completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0
local notation "v" => completeIdentityFirstGraphToChart K n h
local notation "E" => completeIdentityFirstErrorAlgebra K n h (0 : Fin n)
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)
/-- Cache the existing graph ring for evaluating target functions. -/
local instance firstAmbientTargetCommRing : CommRing (E) := inferInstance

/-- Original target functions before imposing the complete graph ideal. -/
def completeIdentityFirstAmbientTargetFunctions : (B) →+* Γ((R), ⊤) :=
  (pullback.snd _ _ : (R) ⟶ chart (A) (t)).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (B))).inv.hom

/-- Original target functions on the full graph chart. -/
def completeIdentityFirstChartTargetFunctions : (B) →+* Γ((H), ⊤) :=
  (completeIdentityActionGraphAdicChartTarget K n h 1 0 0).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (B))).inv.hom
local notation "p" => completeIdentityFirstAmbientTargetFunctions K n h
local notation "q" => completeIdentityFirstChartTargetFunctions K n h

/-- The ambient target restricts to the unchanged chart target. -/
theorem completeIdentityFirstAmbientTargetFunctions_restrict (z : B) :
    (c).appTop ((p) z) = (q) z := by
  change ((Scheme.ΓSpecIso (.of (B))).inv ≫
    (pullback.snd _ _ : (R) ⟶ chart (A) (t)).appTop ≫ (c).appTop) z = _
  rw [← Scheme.Hom.comp_appTop]
  rfl

/-- Evaluation uses the original target with its unchanged coefficient map. -/
theorem completeIdentityFirstChartTargetFunctions_evaluation (z : B) :
    SpectrumGlobalRange.ringHom (v) ((q) z) =
      completeIdentityFirstGraphTarget K n h 0 ((b) z) := by
  have he : (v) ≫ completeIdentityActionGraphAdicChartTarget K n h 1 0 0 =
      Spec.map (CommRingCat.ofHom
        ((completeIdentityFirstGraphTarget K n h 0).toRingHom.comp (b))) := by
    rw [completeIdentityFirstGraphToChart_target, completeIdentityFirstGraphSchemeTarget,
      ← Spec.map_comp]
    rfl
  have hh : (Scheme.ΓSpecIso (.of (B))).inv ≫
      (completeIdentityActionGraphAdicChartTarget K n h 1 0 0).appTop ≫
      (v).appTop ≫ (Scheme.ΓSpecIso (.of (E))).hom =
      CommRingCat.ofHom ((completeIdentityFirstGraphTarget K n h 0).toRingHom.comp (b)) := by
    rw [← Category.assoc (completeIdentityActionGraphAdicChartTarget K n h 1 0 0).appTop,
      ← Scheme.Hom.comp_appTop, he, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun g : CommRingCat.of (B) ⟶ CommRingCat.of (E) ↦ g z) hh

/-- The whole target reduces to reciprocal scaling on the unchanged original source node. -/
theorem completeIdentityFirstAmbientNodeReduction_target (z : B) :
    completeIdentityFirstAmbientNodeReduction K n h ((p) z) =
      firstNodeReduction K[T;T⁻¹] ((σ) ((b) z)) := by
  change completeIdentityFirstChartNodeReduction K n h ((c).appTop ((p) z)) = _
  rw [completeIdentityFirstAmbientTargetFunctions_restrict]
  change completeIdentityFirstGraphReduction K n h 0
    (SpectrumGlobalRange.ringHom (v) ((q) z)) = _
  rw [completeIdentityFirstChartTargetFunctions_evaluation]
  have he := completeIdentityFirstGraphError_reduction K n h 0 ((b) z)
  rw [completeIdentityFirstGraphError] at he
  rw [(completeIdentityFirstGraphReduction K n h 0).map_sub,
    completeIdentityFirstGraphReduction_source, sub_eq_zero] at he
  exact he

end FLT.Mazur.PolygonInfinitesimalStages
