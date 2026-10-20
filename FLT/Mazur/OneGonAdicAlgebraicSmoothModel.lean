/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicFiniteSmoothStage
public import FLT.Mazur.GeneralizedCurveBaseChange
public import FLT.Mazur.CoefficientModelMorphism

/-!
# The enlarged algebraic one-gon and its actual smooth factor

The finite coefficient enlargement carries the base change of the original
generalized one-gon. Its rank-n character source maps into the smooth group,
and the composite is exactly the base change of the fixed closed embedding.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart Approximation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The enlarged finite coefficient subring of the same original complete ring. -/
abbrev smoothModelBase : Subalgebra ℤ R := (algebraicSmoothStage I t ht n).unop.val

instance smoothModelBase_finiteType : Algebra.FiniteType ℤ (smoothModelBase I t ht n) :=
  (algebraicSmoothStage I t ht n).unop.property.2

instance smoothModelBase_finitePresentation :
    Algebra.FinitePresentation ℤ (smoothModelBase I t ht n) :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- The actual inclusion of the initial coefficient spectrum. -/
def smoothModelBaseMap : Spec (.of (smoothModelBase I t ht n)) ⟶
    Spec (.of (algebraicBase I t ht n)) :=
  (coefficientSpectrumToInitial (algebraicBase I t ht n)).app (algebraicSmoothStage I t ht n)

/-- The same generalized one-gon after the chosen coefficient enlargement. -/
def smoothModelCurve : GeneralizedEllipticCurve (Spec (.of (smoothModelBase I t ht n))) :=
  (algebraicCurve I t ht n).baseChange (smoothModelBaseMap I t ht n)

/-- The character source is the actual base change of the fixed rank-n source. -/
abbrev smoothModelCarrier : Over (Spec (.of (smoothModelBase I t ht n))) :=
  (Over.pullback (smoothModelBaseMap I t ht n)).obj (algebraicCarrier I t ht n)

/-- The full model embedding is retained by base change. -/
def smoothModelEmbedding : smoothModelCarrier I t ht n ⟶ (smoothModelCurve I t ht n).curve :=
  (Over.pullback (smoothModelBaseMap I t ht n)).map
    (Over.homMk (algebraicEmbedding I t ht n) (algebraicEmbedding_structure I t ht n))

/-- The descended morphism now lands in the smooth group over the enlarged base. -/
def smoothModelFactor : smoothModelCarrier I t ht n ⟶ (smoothModelCurve I t ht n).group :=
  Over.homMk (pullback.lift (algebraicSmoothFactor I t ht n)
    (pullback.snd (algebraicCarrier I t ht n).hom (smoothModelBaseMap I t ht n)) (by
      exact (algebraicSmoothFactor_structure I t ht n).trans pullback.condition))
    (pullback.lift_snd _ _ _)

/-- Projection retains the descended actual factor. -/
@[reassoc] theorem smoothModelFactor_fst :
    (smoothModelFactor I t ht n).left ≫
      pullback.fst (algebraicCurve I t ht n).group.hom (smoothModelBaseMap I t ht n) =
        algebraicSmoothFactor I t ht n := pullback.lift_fst _ _ _

/-- Its composite into the entire enlarged cubic is exactly the fixed embedding's base change. -/
theorem smoothModelFactor_inclusion :
    smoothModelFactor I t ht n ≫ (smoothModelCurve I t ht n).inclusion =
      smoothModelEmbedding I t ht n := by
  apply Over.OverMorphism.ext
  change (smoothModelFactor I t ht n).left ≫
    ((algebraicCurve I t ht n).baseChange (smoothModelBaseMap I t ht n)).inclusion.left = _
  rw [GeneralizedEllipticCurve.baseChange_inclusion]
  apply pullback.hom_ext
  · rw [Category.assoc]
    change _ ≫ pullback.lift _ _ _ ≫ _ = pullback.lift _ _ _ ≫ _
    rw [pullback.lift_fst, pullback.lift_fst,
      ← Category.assoc, smoothModelFactor_fst]
    exact algebraicSmoothFactor_inclusion I t ht n
  · rw [Category.assoc]
    change _ ≫ pullback.lift _ _ _ ≫ _ = pullback.lift _ _ _ ≫ _
    simp only [pullback.lift_snd]
    exact (smoothModelFactor I t ht n).w

/-- The enlarged source still has exact finite locally free rank n. -/
theorem smoothModelCarrier_degree :
    FCurve.FiniteLocallyFreeDegree (smoothModelCarrier I t ht n).hom n :=
  (algebraicCarrier_degree I t ht n).baseChange (smoothModelBaseMap I t ht n)

end FLT.Mazur.OneGonAdicCharacterTower
