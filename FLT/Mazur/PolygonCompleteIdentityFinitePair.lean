/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteScaling
public import FLT.Mazur.PolygonCompleteIdentityActionMultiplication

/-!
# The actual original identity pair on the finite double Laurent chart

Both finite Laurent inputs are mapped into the original identity group.
Their actual original multiplication contracts to the prescribed cubic
target. No identification of this multiplication with Laurent multiplication
is used in the construction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "U" => completePointIdentityOpen K n h i
local notation "π" => exactVeroneseProjToBase K n h
local notation "e" => completeIdentityStageTorus K n h i m
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i
local notation "q" => completeIdentityFiniteInput K n h i m
local notation "b" => Spec.map (CommRingCat.ofHom
  (algebraMap (A)[T;T⁻¹] (A)[T;T⁻¹][T;T⁻¹]))
local notation "r" => Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap
  (LaurentPolynomial.C : (A) →+* (A)[T;T⁻¹])))

/-- The full finite identity edge retains the first original parameter. -/
@[reassoc] theorem completeIdentityFiniteEdge_fst :
    (j) ≫ (q) ≫ pullback.fst (G).X.hom (π) = (b) ≫ (e) := by
  rw [completeIdentityFiniteInput_fst, edge_toBase_assoc]

/-- The second identity input is the original Laurent coefficient projection. -/
@[reassoc] theorem completeIdentityFiniteEdge_snd :
    (j) ≫ (q) ≫ pullback.snd (G).X.hom (π) = (r) ≫ (e) ≫ (U).ι := by
  rw [completeIdentityFiniteInput_snd, completeIdentityStageTorus_inclusion]
  have he := (edge_parameter_isPullback (t) n h
    (LaurentPolynomial.C : (A) →+* (A)[T;T⁻¹])
    (LaurentPolynomial.C (t)) rfl i).w
  change (r) ≫ edge (A) (t) n h i =
    (j) ≫ scalingParameterProjection (A) (t) n h at he
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ originalStageToCompatibleProj K n h m) he.symm).trans
      (Category.assoc _ _ _))

/-- The full double Laurent scheme maps into the unchanged original group product. -/
def completeIdentityFinitePair :
    PolygonSmoothing.branchTorus (A)[T;T⁻¹] ⟶ ((G).X ⊗ (G).X).left :=
  pullback.lift ((b) ≫ (e)) ((r) ≫ (e)) (by
    have he := congrArg ((j) ≫ (q) ≫ ·)
      (pullback.condition (f := (G).X.hom) (g := (π)))
    rw [completeIdentityFiniteEdge_fst_assoc,
      completeIdentityFiniteEdge_snd_assoc] at he
    simpa only [Category.assoc, completePointOriginalBaseGroup_structure] using he)

/-- The first original identity coordinate is unchanged in the pair. -/
@[reassoc] theorem completeIdentityFinitePair_fst :
    completeIdentityFinitePair K n h i m ≫ pullback.fst (G).X.hom (G).X.hom =
      (b) ≫ (e) := pullback.lift_fst _ _ _

/-- The second original identity coordinate is unchanged in the pair. -/
@[reassoc] theorem completeIdentityFinitePair_snd :
    completeIdentityFinitePair K n h i m ≫ pullback.snd (G).X.hom (G).X.hom =
      (r) ≫ (e) := pullback.lift_snd _ _ _

/-- The original pair reconstructs the exact finite action input on the identity edge. -/
@[reassoc] theorem completeIdentityFinitePair_input :
    completeIdentityFinitePair K n h i m ≫ completeIdentityPairToAction K n h i =
      (j) ≫ (q) := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentityPairToAction_fst,
      completeIdentityFinitePair_fst, Category.assoc, completeIdentityFiniteEdge_fst]
  · rw [Category.assoc, completeIdentityPairToAction_snd,
      completeIdentityFinitePair_snd_assoc, Category.assoc, completeIdentityFiniteEdge_snd]

/-- Actual original multiplication on the full finite double Laurent chart. -/
def completeIdentityFiniteOriginalMul :
    PolygonSmoothing.branchTorus (A)[T;T⁻¹] ⟶ (U).toScheme :=
  completeIdentityFinitePair K n h i m ≫ (μ[(G).X]).left

/-- The constructed actual multiplication retains exactly the prescribed cubic action. -/
@[reassoc] theorem completeIdentityFiniteOriginalMul_cubic :
    completeIdentityFiniteOriginalMul K n h i m ≫ (U).ι ≫
        completePointToIntegralCubic K n h i =
      (j) ≫ (q) ≫ completeIdentityActionTarget K n h i := by
  rw [completeIdentityFiniteOriginalMul, Category.assoc,
    ← completeIdentityPairToAction_target, completeIdentityFinitePair_input_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
