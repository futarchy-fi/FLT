/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineMorphismTensorSection
public import FLT.Mazur.PolygonCompleteLineSectionReconstruction

/-!
# Original stages detect every complete line morphism

Tensor-dual sections turn proper formal section uniqueness into uniqueness
of morphisms between any two actual complete line bundles.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj exactVeroneseProj tensor
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Original finite-stage pullbacks jointly detect morphisms between arbitrary complete lines. -/
theorem completeLineHom_ext_stages {L M : (exactVeroneseProj K n h).Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) (a b : L ⟶ M)
    (hs : ∀ m, (pullback (originalStageToCompatibleProj K n h m)).map a =
      (pullback (originalStageToCompatibleProj K n h m)).map b) : a = b := by
  apply (lineMorphismSectionEquiv hL M).injective
  apply completeLineSection_ext K n h _ (hM.tensor hL.dual)
  intro m
  apply (ConcreteCategory.bijective_of_isIso
    ((lineMorphismTensorPullbackIso hL M (originalStageToCompatibleProj K n h m)).hom.app
      ⊤)).injective
  rw [lineMorphismSectionEquiv_pullback, lineMorphismSectionEquiv_pullback, hs m]

/-- Original stage restrictions jointly detect isomorphisms between arbitrary complete lines. -/
theorem completeLineIso_ext_stages {L M : (exactVeroneseProj K n h).Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) (a b : L ≅ M)
    (hs : ∀ m, (pullback (originalStageToCompatibleProj K n h m)).mapIso a =
      (pullback (originalStageToCompatibleProj K n h m)).mapIso b) : a = b := by
  apply Iso.ext
  exact completeLineHom_ext_stages K n h hL hM a.hom b.hom
    (fun m ↦ congrArg Iso.hom (hs m))

end FLT.Mazur.PolygonInfinitesimalStages
