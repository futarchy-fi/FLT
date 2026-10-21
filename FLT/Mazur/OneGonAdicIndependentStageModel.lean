/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentSmoothStage

public import FLT.Mazur.GeneralizedCurveBaseChange
public import FLT.Mazur.CoefficientModelMorphism

/-!
# Models at arbitrary smooth-stage witnesses

Both the finite support and its smooth stage are inputs. The smooth morphism
is supplied with its whole-cubic factorization; its recovery is derived below.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open OneGonSmoothing WeierstrassIntegralChart Approximation OneGonAdicCharacterTower
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)

/-- The actual finite ring specified by an arbitrary stage witness. -/
abbrev stageBase : Subalgebra ℤ R := i.unop.val

instance stageBase_finiteType : Algebra.FiniteType ℤ (stageBase I t ht n s i) :=
  i.unop.property.2

instance stageBaseAlgebra : Algebra (base I t ht n s) (stageBase I t ht n s i) :=
  (Subalgebra.inclusion i.unop.property.1).toAlgebra

instance stageBase_tower : IsScalarTower (base I t ht n s) (stageBase I t ht n s i) R :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The inclusion of the initial independent support ring. -/
def stageBaseMap : Spec (.of (stageBase I t ht n s i)) ⟶ Spec (.of (base I t ht n s)) :=
  (coefficientSpectrumToInitial (base I t ht n s)).app i

/-- The independently constructed generalized curve at the supplied stage. -/
def stageCurve (hi : complementaryInverse I t ht ∈ s) :
    GeneralizedEllipticCurve (Spec (.of (stageBase I t ht n s i))) :=
  (curve I t ht n s hi).baseChange (stageBaseMap I t ht n s i)

/-- The actual stage pullback of the intrinsic character source. -/
abbrev stageCarrier : Over (Spec (.of (stageBase I t ht n s i))) :=
  (Over.pullback (stageBaseMap I t ht n s i)).obj (carrier I t ht n s)

/-- The whole embedding at the arbitrary stage. -/
def stageEmbedding (hi : complementaryInverse I t ht ∈ s) :
    stageCarrier I t ht n s i ⟶ (stageCurve I t ht n s i hi).curve :=
  (Over.pullback (stageBaseMap I t ht n s i)).map
    (Over.homMk (embedding I t ht n s) (embedding_structure I t ht n s))

/-- The source retains the exact finite locally free degree after enlargement. -/
theorem stageCarrier_degree : FCurve.FiniteLocallyFreeDegree
    (stageCarrier I t ht n s i).hom n :=
  (carrier_degree I t ht n s).baseChange (stageBaseMap I t ht n s i)

variable (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
  (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)

include hb in
/-- The whole-cubic factorization forces the correct structure map. -/
@[reassoc] theorem stageFactor_structure :
    b ≫ integralSmoothStructure (equation (parameter I t ht n s)) =
      (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
        (carrier I t ht n s).hom := by
  change b ≫ (integralSmoothOpen _).ι ≫ _ = _
  rw [← Category.assoc, hb, Category.assoc, embedding_structure]

/-- The supplied smooth factor defines a morphism to the enlarged smooth group. -/
def stageFactor (hi : complementaryInverse I t ht ∈ s) :
    stageCarrier I t ht n s i ⟶ (stageCurve I t ht n s i hi).group :=
  Over.homMk (pullback.lift b
    (pullback.snd (carrier I t ht n s).hom (stageBaseMap I t ht n s i))
    ((stageFactor_structure I t ht n s i b hb).trans pullback.condition))
    (pullback.lift_snd _ _ _)

/-- Its composite with the smooth inclusion is the whole stage embedding. -/
theorem stageFactor_inclusion (hi : complementaryInverse I t ht ∈ s) :
    stageFactor I t ht n s i b hb hi ≫ (stageCurve I t ht n s i hi).inclusion =
      stageEmbedding I t ht n s i hi := by
  apply Over.OverMorphism.ext
  change (stageFactor I t ht n s i b hb hi).left ≫
    ((curve I t ht n s hi).baseChange (stageBaseMap I t ht n s i)).inclusion.left = _
  rw [GeneralizedEllipticCurve.baseChange_inclusion]
  apply pullback.hom_ext
  · change (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ _ = pullback.lift _ _ _ ≫ _
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    exact hb
  · change (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ _ = pullback.lift _ _ _ ≫ _
    simp only [Category.assoc, pullback.lift_snd]

include hb in
/-- Recovery of any stage factor is forced by the full embedding equation. -/
@[reassoc] theorem stageFactor_recovery :
    (coefficientModelCone (base I t ht n s) (carrier I t ht n s).hom).π.app i ≫ b =
      recoveredSmoothFactor I t ht n s := by
  apply (cancel_mono (integralSmoothOpen (equation (parameter I t ht n s))).ι).mp
  rw [Category.assoc, hb, ← Category.assoc, coefficientModelCone_toInitial,
    recoveredSmoothFactor_inclusion]

end FLT.Mazur.OneGonAdicIndependentModel
