/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallySplitResidueCriterion
public import FLT.Mazur.TwistedSectionBaseChange
public import FLT.Mazur.TwistedSectionIntegralCriterion

/-!
# Fiber regularity from locally split direct-image sections

For an integral new total space, invertibility of the actual base-change
mate carries a locally split original line to a nonzero pulled section.
The pulled section uses the original tensor and commutative-square comparisons.
No regularity or flatness of its zero divisor is included as an input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits (comp_zero zero_comp)
open Scheme.Modules
namespace FLT.Mazur.TwistedSectionBaseChangeRegularity
open FCurve ModuleSheafTensor SchemePullbackSquare DirectImageBaseChange
open SplitLineAffineNeighborhood
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor ModuleLineBundleTensorPullback.tensorIso
  twistedSectionPushforwardEquiv moduleSheafDualPullbackIso
variable {P X T S : Scheme.{0}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (L : X.Modules) {B : S.Modules}

/-- Pull the original tensor section through the original square comparison. -/
def section_ (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    Γ(tensor ((pullback p).obj L) ((pullback q).obj ((pullback g).obj B)), ⊤) :=
  (map (𝟙 _) ((squareIso f q g p w).inv.app B)).app ⊤
    ((ModuleLineBundleTensorPullback.tensorIso p L ((pullback f).obj B)).hom.app ⊤
      (pullGlobal p _ s))

variable (hB : LocallyFreeRankOne B)

/-- The independently defined geometric section has the original base-changed map. -/
lemma section_map (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    twistedSectionPushforwardEquiv q ((pullback p).obj L) (hB.pullback g)
      (section_ p q f g w L s) =
    (moduleSheafDualPullbackIso g hB).inv ≫
      (pullback g).map (twistedSectionPushforwardEquiv f L hB s) ≫
        comparison p q f g w L :=
  twistedSectionPushforwardEquiv_baseChange p q f g w L hB s

/-- Local splitting implies regularity on each integral base change where the mate is invertible. -/
theorem regular_of_locallySplit [IsIntegral P] [Nonempty T]
    [IsIso (comparison p q f g w L)] (hL : LocallyFreeRankOne L)
    (s : Γ(tensor L ((pullback f).obj B), ⊤))
    (hs : LocallySplit (twistedSectionPushforwardEquiv f L hB s)) :
    Mono (globalSectionHom _ (section_ p q f g w L s)) := by
  apply (integral_twistedSection_regular_iff q ((pullback p).obj L)
    (hL.pullback p) (hB.pullback g) _).mpr
  rw [section_map p q f g w L hB s]
  intro hz
  apply LocallySplitResidueCriterion.pullback_ne_zero _ hB.dual hs g
  apply (cancel_epi (moduleSheafDualPullbackIso g hB).inv).mp
  apply (cancel_mono (comparison p q f g w L)).mp
  simpa only [Category.assoc, comp_zero, zero_comp] using hz

end FLT.Mazur.TwistedSectionBaseChangeRegularity
