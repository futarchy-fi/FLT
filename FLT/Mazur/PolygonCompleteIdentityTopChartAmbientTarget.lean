/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartClosedPresentation

/-!
# Original target functions in the higher ambient presentation

The unchanged target coordinate map evaluates to the full higher graph
target, retaining the original truncated coefficient map on every function.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "t" => parameter K (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "B" => ChartRing (t)
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "H" => completeIdentityActionGraphAdicChart K n h (m + 1) 0 0
local notation "c" => completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0
local notation "v" => completeIdentityTopGraphToChart K n h m
local notation "E" => completeIdentityTopGraphAlgebra K n h (0 : Fin n) m
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1)
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "g" => topNodeGraphTarget K[T;T⁻¹] m
  (completeIdentityTopActionUnit K n h 0 m)
  (completeIdentityTopActionReciprocalUnit K n h 0 m)
/-- Cache the existing graph ring for evaluating target functions. -/
local instance topAmbientTargetCommRing : CommRing (E) := inferInstance

/-- Original target functions before imposing the complete graph ideal. -/
def completeIdentityTopAmbientTargetFunctions : (B) →+* Γ((R), ⊤) :=
  (pullback.snd _ _ : (R) ⟶ chart (A) (t)).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (B))).inv.hom

/-- Original target functions on the full graph chart. -/
def completeIdentityTopChartTargetFunctions : (B) →+* Γ((H), ⊤) :=
  (completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (B))).inv.hom
local notation "p" => completeIdentityTopAmbientTargetFunctions K n h m
local notation "q" => completeIdentityTopChartTargetFunctions K n h m

/-- The ambient target restricts to the unchanged chart target. -/
theorem completeIdentityTopAmbientTargetFunctions_restrict (z : B) :
    (c).appTop ((p) z) = (q) z := by
  change ((Scheme.ΓSpecIso (.of (B))).inv ≫
    (pullback.snd _ _ : (R) ⟶ chart (A) (t)).appTop ≫ (c).appTop) z = _
  rw [← Scheme.Hom.comp_appTop]
  rfl

/-- Evaluation uses the original target with its unchanged coefficient map. -/
theorem completeIdentityTopChartTargetFunctions_evaluation (z : B) :
    SpectrumGlobalRange.ringHom (v) ((q) z) =
      (g) ((b) z) := by
  have he : (v) ≫ completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0 =
      Spec.map (CommRingCat.ofHom
        ((g).toRingHom.comp (b))) := by
    rw [completeIdentityTopGraphToChart_target]
    change Spec.map (CommRingCat.ofHom (g).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (b)) = _
    rw [← Spec.map_comp]
    rfl
  have hh : (Scheme.ΓSpecIso (.of (B))).inv ≫
      (completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0).appTop ≫
      (v).appTop ≫ (Scheme.ΓSpecIso (.of (E))).hom =
      CommRingCat.ofHom ((g).toRingHom.comp (b)) := by
    rw [← Category.assoc (completeIdentityActionGraphAdicChartTarget K n h (m + 1) 0 0).appTop,
      ← Scheme.Hom.comp_appTop, he, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg (fun φ : CommRingCat.of (B) ⟶ CommRingCat.of (E) ↦ φ z) hh

end FLT.Mazur.PolygonInfinitesimalStages
