/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityStageTorus
public import FLT.Mazur.PolygonInfinitesimalScalingProduct
public import FLT.Mazur.PolygonCompleteIdentityActionTarget

/-!
# Polygon-valued scaling on the actual finite identity-action inputs

The variable-parameter polygon is the original whole action input's actual
adic base change. Its constructed scaling is polygon-valued at every finite
order. Equality with the prescribed cubic action is a further comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "p" => originalStageToCompatibleProj K n h m
local notation "π" => exactVeroneseProjToBase K n h
local notation "q" => toBase A[T;T⁻¹] (LaurentPolynomial.C (t)) n h
local notation "r" => scalingParameterProjection (A) (t) n h
local notation "e" => completeIdentityStageTorus K n h i m
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (A) (A)[T;T⁻¹]))

/-- The finite Laurent parameter is the actual original identity group's adic base change. -/
theorem completeIdentityFiniteParameter_isPullback :
    IsPullback (e) (b) (G).X.hom (baseToSeries K m) := by
  rw [completePointOriginalBaseGroup_structure]
  exact completeIdentityStageTorus_base_isPullback K n h i m

/-- The full variable-parameter stage maps to the original, unchanged action input product. -/
def completeIdentityFiniteInput :
    scalingParameterFamily (A) (t) n h ⟶ completeIdentityActionProduct K n h i :=
  pullback.lift ((q) ≫ (e)) ((r) ≫ (p)) (by
    rw [Category.assoc, (completeIdentityFiniteParameter_isPullback K n h i m).w,
      Category.assoc, originalStageToCompatibleProj_toBase]
    change (q) ≫ (b) ≫ baseToSeries K m =
      (r) ≫ toBase (A) (t) n h ≫ baseToSeries K m
    rw [scalingParameterProjection, parameterProjection_base_assoc]
    rfl)

/-- The first input is the actual original identity parameter, with every nilpotent retained. -/
@[reassoc] theorem completeIdentityFiniteInput_fst :
    completeIdentityFiniteInput K n h i m ≫ pullback.fst _ _ = (q) ≫ (e) :=
  pullback.lift_fst _ _ _

/-- The second input is the actual whole original stage, including every node. -/
@[reassoc] theorem completeIdentityFiniteInput_snd :
    completeIdentityFiniteInput K n h i m ≫ pullback.snd _ _ = (r) ≫ (p) :=
  pullback.lift_snd _ _ _

/-- The variable-parameter stage is the actual input pullback along the original stage. -/
theorem completeIdentityFiniteInput_isPullback :
    IsPullback (completeIdentityFiniteInput K n h i m) (r)
      (pullback.snd (G).X.hom (π)) (p) := by
  have hp := (parameterProjection_isPullback
    (LaurentPolynomial.C : (A) →+* (A)[T;T⁻¹]) (t) (LaurentPolynomial.C (t))
    rfl n h).flip.paste_horiz (completeIdentityFiniteParameter_isPullback K n h i m)
  have hp' : IsPullback
      (completeIdentityFiniteInput K n h i m ≫ pullback.fst (G).X.hom (π))
      (r) (G).X.hom ((p) ≫ (π)) := by
    rw [completeIdentityFiniteInput_fst, originalStageToCompatibleProj_toBase]
    exact hp
  exact hp'.of_right (completeIdentityFiniteInput_snd K n h i m)
    (IsPullback.of_hasPullback (G).X.hom (π))

/-- The same constructed source is the whole input's actual finite adic base change. -/
theorem completeIdentityFiniteInput_base_isPullback :
    IsPullback (completeIdentityFiniteInput K n h i m)
      ((r) ≫ (family K m n h).hom)
      (pullback.snd (G).X.hom (π) ≫ (π)) (baseToSeries K m) :=
  (completeIdentityFiniteInput_isPullback K n h i m).paste_vert
    (originalStageToCompatibleProj_isPullback K n h m)

/-- A constructed polygon-valued map on the entire original finite-order input. -/
def completeIdentityFiniteScaling :
    scalingParameterFamily (A) (t) n h ⟶ exactVeroneseProj K n h :=
  universalScaling (A) (t) n h ≫ (p)

/-- The finite scaling retains the unchanged original power-series base. -/
@[reassoc] theorem completeIdentityFiniteScaling_base :
    completeIdentityFiniteScaling K n h m ≫ (π) =
      completeIdentityFiniteInput K n h i m ≫ pullback.snd _ _ ≫ (π) := by
  rw [completeIdentityFiniteScaling, Category.assoc,
    originalStageToCompatibleProj_toBase, completeIdentityFiniteInput_snd_assoc]
  change universalScaling (A) (t) n h ≫ toBase (A) (t) n h ≫ baseToSeries K m = _
  rw [universalScaling_base_assoc, originalStageToCompatibleProj_toBase]
  change _ = (r) ≫ toBase (A) (t) n h ≫ baseToSeries K m
  rw [scalingParameterProjection, parameterProjection_base_assoc]

/-- Every coefficient-unit specialization retains the original whole-stage automorphism. -/
@[reassoc] theorem completeIdentityFiniteScaling_specialize (a : (A)ˣ) :
    scalingParameterSection (A) (t) n h a ≫ completeIdentityFiniteScaling K n h m =
      scaling (A) (t) n h a ≫ (p) := by
  rw [completeIdentityFiniteScaling, scalingParameterSection_universalScaling_assoc]

/-- The unit parameter fixes the entire original finite stage, including all node inputs. -/
@[reassoc] theorem completeIdentityFiniteScaling_one :
    scalingParameterSection (A) (t) n h 1 ≫ completeIdentityFiniteScaling K n h m = (p) := by
  rw [completeIdentityFiniteScaling_specialize, scaling_one, Category.id_comp]

/-- The same unit section is the actual original zero-action input, not a chosen substitute. -/
@[reassoc] theorem completeIdentityFiniteInput_one :
    scalingParameterSection (A) (t) n h 1 ≫ completeIdentityFiniteInput K n h i m =
      (p) ≫ completeIdentityActionZeroGraph K n h i := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentityFiniteInput_fst, Category.assoc,
      completeIdentityActionZeroGraph, pullback.lift_fst,
      scalingParameterSection, parameterProjection_base_assoc]
    change toBase (A) (t) n h ≫
        PolygonSmoothing.markedTorusSection (1 : (A)ˣ) ≫ (e) =
      (p) ≫ (π) ≫ completePointIdentityMarking K n h i
    rw [completeIdentityStageTorus_one, originalStageToCompatibleProj_toBase_assoc]
    rfl
  · rw [Category.assoc, completeIdentityFiniteInput_snd, Category.assoc,
      completeIdentityActionZeroGraph, pullback.lift_snd,
      scalingParameterSection_projection_assoc, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages
