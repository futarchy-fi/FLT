/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantAffineComparison
public import FLT.Mazur.LocallyRingedOpenInclusion

/-!
# Naturality of the actual orbit-open affine comparisons

The canonical comparisons commute with every restriction of orbit opens. Both
horizontal maps use the original sheaf restriction, including the transport
between open sections and global sections of locally ringed restrictions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {V W : Opens (Orbit n)} (h : V ≤ W)

/-- The actual inclusion between locally ringed orbit-open restrictions. -/
def invariantOpenInclusion : invariantOpenSpace n V ⟶ invariantOpenSpace n W :=
  LocallyRingedOpenInclusion.inclusion (invariantLocallyRingedSpace n) h

/-- Orbit-open inclusions retain the original points. -/
theorem invariantOpenInclusion_base (x : V) :
    (invariantOpenInclusion n h).base x = ⟨x.val, h x.property⟩ :=
  LocallyRingedOpenInclusion.inclusion_base (invariantLocallyRingedSpace n) h x

/-- These are actual open immersions of locally ringed spaces. -/
instance invariantOpenInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (invariantOpenInclusion n h) :=
  LocallyRingedOpenInclusion.inclusion_isOpenImmersion _ h

/-- Pullback of global sections is precisely the original invariant sheaf restriction. -/
theorem invariantOpenInclusion_sections :
    (invariantOpenSectionsIso n W).inv ≫
      LocallyRingedSpace.Γ.map (invariantOpenInclusion n h).op =
        (invariantSheaf n).obj.map (homOfLE h).op ≫ (invariantOpenSectionsIso n V).inv :=
  LocallyRingedOpenInclusion.inclusion_sections _ h

/-- The affine target morphism induced by actual invariant restriction. -/
def invariantAffineRestriction : invariantAffineTarget n V ⟶ invariantAffineTarget n W :=
  Spec.map ((invariantSheaf n).obj.map (homOfLE h).op)

/-- Canonical affine comparisons commute with all actual orbit-open inclusions. -/
@[reassoc] theorem invariantAffineComparison_naturality :
    invariantOpenInclusion n h ≫ invariantAffineComparison n W =
      invariantAffineComparison n V ≫ (invariantAffineRestriction n h).toLRSHom := by
  have H := identityToΓSpec.naturality (invariantOpenInclusion n h)
  change invariantOpenInclusion n h ≫ (invariantOpenSpace n W).toΓSpec =
    (invariantOpenSpace n V).toΓSpec ≫
      Spec.locallyRingedSpaceMap (LocallyRingedSpace.Γ.map (invariantOpenInclusion n h).op)
    at H
  unfold invariantAffineComparison invariantAffineRestriction
  rw [← Category.assoc, H, Category.assoc]
  change _ = _ ≫ Spec.locallyRingedSpaceMap _
  rw [Category.assoc, ← Spec.locallyRingedSpaceMap_comp,
    ← Spec.locallyRingedSpaceMap_comp, invariantOpenInclusion_sections]

end FLT.Mazur.CyclicCharacteristicOrbit
