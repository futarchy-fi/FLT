/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorCanonicalSection
public import FLT.Mazur.ModuleSheafDualPullbackUnit
public import FLT.Mazur.PolygonIdealModulePullback
public import FLT.Mazur.ProjectiveLineMarkedCharts

/-!
# The positive divisor comparison on polygon normalization

The actual ideal-module isomorphism induces a comparison of the positive
divisor sheaves. The comparison preserves the dual pairing and the canonical
section. Its invertibility requires dual pullback for locally trivial modules.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.PolygonDivisorLineComparison
open PolygonPinching PolygonDivisorNormalizationPullback FCurve
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The canonical morphism from the pulled-back polygon line to the marked-point line. -/
def comparison (a : Fin n → Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).obj
      (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a)
        (PolygonBoundaryDivisor.cartier K n p hn q h a).1) ⟶
      divisorLineBundle (markedPoint K (a i)).ker
        (ProjectiveLineMarkedCharts.relativeCartier K (a i)).1 :=
  moduleSheafDualPullbackViaIso (componentι K n i ≫ p).left
    (idealModule (PolygonBoundaryDivisor.ideal K n p a))
      (PolygonIdealModulePullback.idealIso K n hn p q h a i)

/-- The positive comparison preserves evaluation against the actual ideal isomorphism. -/
lemma comparison_eval (a : Fin n → Kˣ) (i : Fin n) (U : (ProjectiveLine.scheme K).Opens)
    (φ : Γ((Scheme.Modules.pullback (componentι K n i ≫ p).left).obj
      (moduleSheafDual (idealModule (PolygonBoundaryDivisor.ideal K n p a))), U))
    (s : Γ((Scheme.Modules.pullback (componentι K n i ≫ p).left).obj
      (idealModule (PolygonBoundaryDivisor.ideal K n p a)), U)) :
    moduleDualEval (idealModule (markedPoint K (a i)).ker) U
      ((comparison K n hn p q h a i).app U φ)
        ((PolygonIdealModulePullback.idealIso K n hn p q h a i).hom.app U s) =
    (moduleDualPullbackPairing (componentι K n i ≫ p).left
      (idealModule (PolygonBoundaryDivisor.ideal K n p a))).app U
        (ModuleSheafTensor.pure _ _ U φ s) :=
  moduleSheafDualPullbackViaIso_eval (componentι K n i ≫ p).left
    (idealModule (PolygonBoundaryDivisor.ideal K n p a))
    (PolygonIdealModulePullback.idealIso K n hn p q h a i) U φ s

/-- The positive comparison carries the canonical polygon section to the marked section. -/
@[reassoc]
lemma comparison_section (a : Fin n → Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).map
      (divisorSectionMap (PolygonBoundaryDivisor.cartier K n p hn q h a).1) ≫
        comparison K n hn p q h a i =
    (modulePullbackUnitIso (componentι K n i ≫ p).left).hom ≫
      divisorSectionMap (ProjectiveLineMarkedCharts.relativeCartier K (a i)).1 :=
  moduleSheafDualPullbackViaIso_section (componentι K n i ≫ p).left
    (PolygonIdealModulePullback.idealIso K n hn p q h a i)
    (idealModuleι (PolygonBoundaryDivisor.ideal K n p a))
    (idealModuleι (markedPoint K (a i)).ker)
    (PolygonIdealModulePullback.idealIso_ι K n hn p q h a i)

end FLT.Mazur.PolygonDivisorLineComparison
