/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityResidueSmooth
public import FLT.Mazur.WeierstrassSplitNodalSmoothGroupComparison

/-!
# The original residue smooth group retains its Laurent law

The full smooth cubic group comparison uses the original addition and zero
morphisms. Its carrier is exactly the previously constructed geometric isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Equation equality retains the original smooth cubic group, including its original law. -/
def splitEquationSmoothGroupIso {K : Type u} [CommRing K] {U : WeierstrassCurve K}
    (a : Kˣ) (h : U = splitNodalEquation a) :
    integralSmoothGroup U ≅ CommGrp.mk (MultiplicativeGroupScheme.gm K) := by
  subst U
  exact integralSmoothSplitNodalTorusIso a

/-- The group comparison is the inverse of the full original smooth Laurent chart. -/
theorem splitEquationSmoothGroupIso_hom {K : Type u} [CommRing K]
    {U : WeierstrassCurve K} (a : Kˣ) (h : U = splitNodalEquation a) :
    (splitEquationSmoothGroupIso a h).hom.hom.hom.hom.left =
      (splitEquationSmoothIso a h).inv := by
  subst U
  exact congrArg Over.Hom.left (integralSmoothSplitNodalTorusIso_hom a)

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "V" => W.map (algebraMap R K)

/-- The actual original residue smooth cubic group is the multiplicative group. -/
def infinityResidueSmoothGroupIso :
    integralSmoothGroup V ≅ CommGrp.mk (MultiplicativeGroupScheme.gm K) :=
  splitEquationSmoothGroupIso (WeierstrassDilatation.residueTangentUnit D)
    (splitDepth_residue_equation D hdepth)

/-- The smooth group comparison retains the entire original geometric contraction chart. -/
theorem infinityResidueSmoothGroupIso_hom :
    (infinityResidueSmoothGroupIso D hdepth).hom.hom.hom.hom.left =
      (infinityResidueSmoothIso D hdepth).inv :=
  splitEquationSmoothGroupIso_hom _ _

/-- The inverse group comparison has the original smooth Laurent parametrization. -/
theorem infinityResidueSmoothGroupIso_inv :
    (infinityResidueSmoothGroupIso D hdepth).inv.hom.hom.hom.left =
      (infinityResidueSmoothIso D hdepth).hom := by
  apply (cancel_mono (infinityResidueSmoothIso D hdepth).inv).mp
  rw [Iso.hom_inv_id, ← infinityResidueSmoothGroupIso_hom]
  change ((infinityResidueSmoothGroupIso D hdepth).inv ≫
    (infinityResidueSmoothGroupIso D hdepth).hom).hom.hom.hom.left = _
  rw [Iso.inv_hom_id]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
