/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveIteratedProjection
public import FLT.Mazur.GeneralizedCurveMarkedCubicCocycle
public import FLT.Mazur.GeneralizedCurveMarkingOverlapCubic

/-!
# Triple-overlap coherence for independently restricted cubic charts

Three base charts restricted to a common base have canonical full-family
transitions satisfying the cocycle. Their constructed cubic transitions inherit
this equality for three independent frames of the original marking lines.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FCurve.divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve markedCubicComparison
variable {S T U Z V : Scheme} (E : GeneralizedEllipticCurve S)
  (g : T ⟶ S) (h : U ⟶ S) (k : Z ⟶ S)
  (p : V ⟶ T) (q : V ⟶ U) (r : V ⟶ Z)
  (w : q ≫ h = p ≫ g) (v : r ≫ k = q ≫ h)

/-- The canonical full-family transitions on three chart paths satisfy the cocycle. -/
theorem smoothMarkingOverlap_comp :
    (baseChangeSquare h k r q v).app E ≪≫ (baseChangeSquare g h q p w).app E =
      (baseChangeSquare g k r p (v.trans w)).app E := by
  apply Iso.ext
  apply E.baseChange_twice_hom_ext g p
  change (((baseChangeSquare h k r q v).app E).hom.curve.left ≫
    ((baseChangeSquare g h q p w).app E).hom.curve.left) ≫ _ = _
  rw [Category.assoc, smoothMarkingOverlap_projection,
    smoothMarkingOverlap_projection, smoothMarkingOverlap_projection]

variable [IsAffine V] [IsNoetherianRing Γ(V, ⊤)]
  (s : 𝟙_ (Over S) ⟶ E.group)
  (a : SmoothMarkingFrame ((E.baseChange g).baseChange p) (pullSection p (pullSection g s)))
  (b : SmoothMarkingFrame ((E.baseChange h).baseChange q) (pullSection q (pullSection h s)))
  (c : SmoothMarkingFrame ((E.baseChange k).baseChange r) (pullSection r (pullSection k s)))

/-- The three independently framed cubic overlap transitions satisfy the actual cocycle. -/
theorem smoothMarkingOverlapCubicIso_comp :
    smoothMarkingOverlapCubicIso E g h p q w s a b ≪≫
      smoothMarkingOverlapCubicIso E h k q r v s b c =
        smoothMarkingOverlapCubicIso E g k p r (v.trans w) s a c := by
  unfold smoothMarkingOverlapCubicIso
  rw [markedCubicComparison_comp]
  congr 1
  exact smoothMarkingOverlap_comp E g h k p q r w v

end FLT.Mazur.GeneralizedEllipticCurve
