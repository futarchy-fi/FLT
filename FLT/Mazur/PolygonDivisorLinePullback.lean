/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDualPullbackRestrict
public import FLT.Mazur.PolygonDivisorLineComparison

/-!
# The positive divisor line on polygon normalization

The canonical comparison is an isomorphism by local freeness of the Cartier
ideal. Its original pairing and section identities are retained, including
self-pinching and both components of the two-gon.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonDivisorLineComparison
open PolygonPinching PolygonDivisorNormalizationPullback FCurve
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
/-- The actual positive polygon comparison is invertible on every component. -/
instance comparison_isIso (a : Fin n → Kˣ) (i : Fin n) :
    IsIso (comparison K n hn p q h a i) := by
  have := moduleSheafDualPullbackHom_isIso_of_locallyFreeRankOne
    (componentι K n i ≫ p).left
    (PolygonBoundaryDivisor.cartier K n p hn q h a).1.idealModule_locallyFreeRankOne
  dsimp only [comparison, moduleSheafDualPullbackViaIso]
  infer_instance

/-- The positive divisor line pulls back to the marked-point line. -/
def lineIso (a : Fin n → Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).obj
      (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a)
        (PolygonBoundaryDivisor.cartier K n p hn q h a).1) ≅
      divisorLineBundle (markedPoint K (a i)).ker
        (ProjectiveLineMarkedCharts.relativeCartier K (a i)).1 :=
  asIso (comparison K n hn p q h a i)

/-- The isomorphism has the existing canonical comparison as its forward map. -/
@[simp]
lemma lineIso_hom (a : Fin n → Kˣ) (i : Fin n) :
    (lineIso K n hn p q h a i).hom = comparison K n hn p q h a i := rfl
/-- The positive comparison preserves evaluation against the actual ideal isomorphism. -/
lemma lineIso_eval (a : Fin n → Kˣ) (i : Fin n) (U : (ProjectiveLine.scheme K).Opens)
    (φ : Γ((Scheme.Modules.pullback (componentι K n i ≫ p).left).obj
      (moduleSheafDual (idealModule (PolygonBoundaryDivisor.ideal K n p a))), U))
    (s : Γ((Scheme.Modules.pullback (componentι K n i ≫ p).left).obj
      (idealModule (PolygonBoundaryDivisor.ideal K n p a)), U)) :
    moduleDualEval (idealModule (markedPoint K (a i)).ker) U
      ((lineIso K n hn p q h a i).hom.app U φ)
        ((PolygonIdealModulePullback.idealIso K n hn p q h a i).hom.app U s) =
    (moduleDualPullbackPairing (componentι K n i ≫ p).left
      (idealModule (PolygonBoundaryDivisor.ideal K n p a))).app U
        (ModuleSheafTensor.pure _ _ U φ s) :=
  moduleSheafDualPullbackViaIso_eval (componentι K n i ≫ p).left
    (idealModule (PolygonBoundaryDivisor.ideal K n p a))
    (PolygonIdealModulePullback.idealIso K n hn p q h a i) U φ s

/-- The positive comparison carries the canonical polygon section to the marked section. -/
@[reassoc]
lemma lineIso_section (a : Fin n → Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).map
      (divisorSectionMap (PolygonBoundaryDivisor.cartier K n p hn q h a).1) ≫
        (lineIso K n hn p q h a i).hom =
    (modulePullbackUnitIso (componentι K n i ≫ p).left).hom ≫
      divisorSectionMap (ProjectiveLineMarkedCharts.relativeCartier K (a i)).1 :=
  moduleSheafDualPullbackViaIso_section (componentι K n i ≫ p).left
    (PolygonIdealModulePullback.idealIso K n hn p q h a i)
    (idealModuleι (PolygonBoundaryDivisor.ideal K n p a))
    (idealModuleι (markedPoint K (a i)).ker)
    (PolygonIdealModulePullback.idealIso_ι K n hn p q h a i)

end FLT.Mazur.PolygonDivisorLineComparison
