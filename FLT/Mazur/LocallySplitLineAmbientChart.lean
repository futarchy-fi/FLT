/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineProjectiveNaturality
public import FLT.Mazur.LocallySplitSheafTransport
public import FLT.Mazur.LocallyFreeDualProjectiveAtlas

/-!
# Reverse points in varying finite free ambient charts

An actual locally split line inside an arbitrary module sheaf gives a
projective point on each finite free ambient chart, even when the source line
is nontrivial on that chart. The point maps into the actual dual projective
atlas and lies over the original chart inclusion. Transition compatibility
of these maps remains a separate theorem.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.LocallySplitLineAmbientChart
open FCurve SplitLineAffineNeighborhood ProjectiveSpace
variable {X : Scheme.{u}} {L M : X.Modules} (s : L ⟶ M)
variable (hL : LocallyFreeRankOne L) (hs : LocallySplit s)
variable (U : X.Opens) {ι : Type u}
variable (e : M.restrict U.ι ≅ SheafOfModules.free ι)

/-- The original inclusion expressed in the chosen ambient chart. -/
def inclusion : L.restrict U.ι ⟶ SheafOfModules.free ι :=
  (restrictFunctor U.ι).map s ≫ e.hom

include hs in
/-- Chart coordinates preserve actual local splitting. -/
lemma inclusion_locallySplit : LocallySplit (inclusion s U e) :=
  (hs.restriction s U.ι).postcompose _ e

variable [Finite ι]

/-- Local source frames construct the reverse point throughout the ambient chart. -/
def point : U.toScheme ⟶ space Γ(U.toScheme, ⊤) ι :=
  SplitLineAffinePresentation.morphism (inclusion s U e) (hL.restrict U.ι)
    (inclusion_locallySplit s hs U e)

/-- The actual chart point lies over its original coefficient spectrum. -/
lemma point_baseProjection : point s hL hs U e ≫ baseProjection Γ(U.toScheme, ⊤) ι =
    U.toScheme.toSpecΓ :=
  SplitLineAffinePresentation.morphism_baseProjection _ _ _

/-- Over an affine ambient chart the point is a section of the projective projection. -/
lemma point_affineProjection [IsAffine U.toScheme] :
    point s hL hs U e ≫ affineProjection U.toScheme ι = 𝟙 U.toScheme := by
  rw [affineProjection, ← Category.assoc, point_baseProjection,
    Scheme.toSpecΓ_isoSpec_inv]

variable (hM : LocallyFiniteFree M)

/-- The reverse point maps into the actual glued projective atlas on each ambient chart. -/
def atlasPoint (i : AffineFiniteFreeAtlas.Index M) :
    i.val.toScheme ⟶ LocallyFreeDualProjectiveAtlas.space M hM :=
  point s hL hs i.val (AffineFiniteFreeAtlas.chart M i) ≫
    LocallyFreeDualProjectiveAtlas.chartMap M hM i

/-- Every constructed atlas point lies over the original base chart inclusion. -/
lemma atlasPoint_projection (i : AffineFiniteFreeAtlas.Index M) :
    atlasPoint s hL hs hM i ≫ LocallyFreeDualProjectiveAtlas.projection M hM = i.val.ι := by
  rw [atlasPoint, Category.assoc, LocallyFreeDualProjectiveAtlas.chart_projection,
    ← Category.assoc, point_affineProjection, Category.id_comp]

end FLT.Mazur.LocallySplitLineAmbientChart
