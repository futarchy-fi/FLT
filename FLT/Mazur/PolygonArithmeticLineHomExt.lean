/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LineMorphismTensorSection
public import FLT.Mazur.PolygonArithmeticLineSectionReconstruction

/-!
# Original stages detect every complete line morphism

Tensor-dual sections turn proper formal section uniqueness into uniqueness
of morphisms between any two actual complete line bundles.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonArithmeticStages
open FCurve ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] originalStageToCompatibleProj exactVeroneseProj tensor
variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Original finite-stage pullbacks jointly detect morphisms between arbitrary complete lines. -/
theorem completeLineHom_ext_stages {L M : (exactVeroneseProj A π n h hne hgen).Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) (a b : L ⟶ M)
    (hs : ∀ m, (pullback (originalStageToCompatibleProj A π hne hgen n h m)).map a =
      (pullback (originalStageToCompatibleProj A π hne hgen n h m)).map b) : a = b := by
  apply (lineMorphismSectionEquiv hL M).injective
  apply completeLineSection_ext A π hne hgen n h _ (hM.tensor hL.dual)
  intro m
  apply (ConcreteCategory.bijective_of_isIso
    ((lineMorphismTensorPullbackIso hL M (originalStageToCompatibleProj A π hne hgen n h m)).hom.app
      ⊤)).injective
  rw [lineMorphismSectionEquiv_pullback, lineMorphismSectionEquiv_pullback, hs m]

/-- Original stage restrictions jointly detect isomorphisms between arbitrary complete lines. -/
theorem completeLineIso_ext_stages {L M : (exactVeroneseProj A π n h hne hgen).Modules}
    (hL : LocallyFreeRankOne L) (hM : LocallyFreeRankOne M) (a b : L ≅ M)
    (hs : ∀ m, (pullback (originalStageToCompatibleProj A π hne hgen n h m)).mapIso a =
      (pullback (originalStageToCompatibleProj A π hne hgen n h m)).mapIso b) : a = b := by
  apply Iso.ext
  exact completeLineHom_ext_stages A π hne hgen n h hL hM a.hom b.hom
    (fun m ↦ congrArg Iso.hom (hs m))

end FLT.Mazur.PolygonArithmeticStages
