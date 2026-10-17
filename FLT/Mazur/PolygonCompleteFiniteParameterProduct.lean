/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteParameterTranslation
public import FLT.Mazur.PolygonCompleteWholeActionFinite

/-!
# The finite Laurent family is the actual original parameter product

The comparison retains both the whole original polygon and the finite Laurent
parameter, including all nilpotents. Its parameter is the original smooth chart.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "X" => completeOriginalWholeOver K n h
local notation "q" => toBase (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h
local notation "r" => scalingParameterProjection (A) (t) n h
local notation "p" => originalStageToCompatibleProj K n h m

/-- The original finite Laurent parameter scheme over the complete arithmetic base. -/
def completeFiniteParameterOver : Over (Spec (.of (PowerSeries K))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (A) (A)[T;T⁻¹])) ≫ baseToSeries K m)

/-- The finite parameter is the actual original smooth point in each rotation chart. -/
def completeFiniteParameter (b : ZMod n) :
    completeFiniteParameterOver K m ⟶ completeOriginalSmoothOver K n h :=
  Over.homMk (V := (completePointOriginalBaseGroup K n h 0).X)
    (completeIdentityStageTorus K n h 0 m)
    (completeIdentityFiniteParameter_isPullback K n h 0 m).w ≫
      completeIdentityChart K n h 0 b

/-- The finite Laurent polygon is the whole original family pulled back to its parameter. -/
theorem completeFiniteParameterProduct_isPullback :
    IsPullback ((r) ≫ (p)) (q) (X).hom (completeFiniteParameterOver K m).hom :=
  (parameterProjection_isPullback LaurentPolynomial.C (t) (LaurentPolynomial.C (t))
    rfl n h).paste_horiz (originalStageToCompatibleProj_isPullback K n h m)

/-- The comparison is an isomorphism onto the actual categorical parameter product. -/
def completeFiniteParameterProductIso :
    scalingParameterFamily (A) (t) n h ≅ ((X) ⊗ completeFiniteParameterOver K m).left :=
  (completeFiniteParameterProduct_isPullback K n h m).isoPullback

/-- The product comparison preserves the original whole input, including singular points. -/
@[reassoc] theorem completeFiniteParameterProductIso_fst :
    (completeFiniteParameterProductIso K n h m).hom ≫
      (fst (X) (completeFiniteParameterOver K m)).left = (r) ≫ (p) :=
  (completeFiniteParameterProduct_isPullback K n h m).isoPullback_hom_fst

/-- The product comparison preserves the actual finite Laurent parameter. -/
@[reassoc] theorem completeFiniteParameterProductIso_snd :
    (completeFiniteParameterProductIso K n h m).hom ≫
      (snd (X) (completeFiniteParameterOver K m)).left = (q) :=
  (completeFiniteParameterProduct_isPullback K n h m).isoPullback_hom_snd

end FLT.Mazur.PolygonInfinitesimalStages
