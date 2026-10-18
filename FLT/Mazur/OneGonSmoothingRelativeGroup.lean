/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingFamily
public import FLT.Mazur.WeierstrassSmoothGroup

/-!
# The smooth group of the whole one-gon smoothing

The group and its open embedding exist over the complete base, including the
singular closed fiber. Arbitrary base changes retain the original cubic.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (t : R)

/-- The smooth group over the entire coefficient spectrum, including bad reduction. -/
def relativeGroup : CommGrp (Over (Spec (.of R))) := integralSmoothGroup (equation t)

/-- The actual open embedding in the original proper smoothing family. -/
def relativeGroupInclusion : (relativeGroup t).X ⟶ family t :=
  Over.homMk (integralSmoothOpen (equation t)).ι rfl

/-- The group embedding is the original relative smooth open. -/
instance relativeGroupInclusion_open : IsOpenImmersion (relativeGroupInclusion t).left :=
  inferInstanceAs (IsOpenImmersion (integralSmoothOpen (equation t)).ι)

/-- The smooth group is separated over the complete coefficient spectrum. -/
instance relativeGroup_separated : IsSeparated (relativeGroup t).X.hom := by
  let _ := family_proper t
  rw [← (relativeGroupInclusion t).w]
  infer_instance

/-- Its identity retains the actual infinity marking on the whole cubic. -/
theorem relativeGroup_identity :
    (η[(relativeGroup t).X] ≫ relativeGroupInclusion t).left = marking t :=
  integralSmoothZero_inclusion (equation t)

variable {T : Scheme} (g : T ⟶ Spec (.of R))

/-- The original smooth group pulled back to any test over the complete base. -/
def relativeTestGroup : CommGrp (Over T) :=
  (Over.pullback g).mapCommGrp.obj (relativeGroup t)

/-- The group test embeds in the pullback of the entire original cubic. -/
def relativeTestInclusion :
    (relativeTestGroup t g).X ⟶ (Over.pullback g).obj (family t) :=
  (Over.pullback g).map (relativeGroupInclusion t)

/-- Base change retains the actual original open immersion. -/
instance relativeTestInclusion_open : IsOpenImmersion (relativeTestInclusion t g).left := by
  change IsOpenImmersion (pullback.map _ _ _ _ (relativeGroupInclusion t).left (𝟙 _) (𝟙 _)
    (by simp) (by simp))
  infer_instance

/-- The pulled-back group remains separated over an arbitrary test scheme. -/
instance relativeTestGroup_separated : IsSeparated (relativeTestGroup t g).X.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (relativeGroup t).X.hom g))

/-- The original cubic remains proper over every such test. -/
theorem relativeTestFamily_proper : IsProper ((Over.pullback g).obj (family t)).hom := by
  let _ := family_proper t
  exact inferInstanceAs (IsProper (pullback.snd (family t).hom g))

end FLT.Mazur.OneGonSmoothing
