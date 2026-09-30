/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowFiniteSegreEmbedding
public import FLT.Mazur.ChowGraphRestriction
public import FLT.Mazur.RelativeVeryAmpleLineBundle

/-!
# A simultaneous very ample line bundle on the Chow modification

For a proper scheme over a field, the Chow projective immersion is closed.
Its hyperplane bundle is relatively very ample both for the modification
and for the map to the field. The relative closed embedding is the pair
of the modification and the projective immersion. All sheaves and powers
below are actual module sheaves; ampleness is proved from properness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open FLT.Mazur.ProjectiveSpace FLT.Mazur.FCurve
open FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The projective space over the original source used by the second presentation. -/
def graphRelativeProjectiveSpace : Scheme :=
  pullback f (baseProjection k (Fin (graphProjectiveDimension f + 1)))

/-- The relative projective embedding is exactly the pair `(π, i)`. -/
def graphRelativeProjectiveEmbedding : graphClosure f ⟶ graphRelativeProjectiveSpace f :=
  pullback.lift (graphClosureπ f) (graphProjectiveImmersion f)
    (graphProjectiveImmersion_baseProjection f).symm

/-- The first coordinate of the relative embedding is the modification. -/
@[reassoc (attr := simp)]
lemma graphRelativeProjectiveEmbedding_fst :
    graphRelativeProjectiveEmbedding f ≫ pullback.fst _ _ = graphClosureπ f :=
  pullback.lift_fst _ _ _

/-- The second coordinate of the relative embedding is the absolute projective embedding. -/
@[reassoc (attr := simp)]
lemma graphRelativeProjectiveEmbedding_snd :
    graphRelativeProjectiveEmbedding f ≫ pullback.snd _ _ = graphProjectiveImmersion f :=
  pullback.lift_snd _ _ _

/-- The pair `(π, i)` is a closed immersion, with no extra geometric hypotheses. -/
instance graphRelativeProjectiveEmbedding_isClosedImmersion :
    IsClosedImmersion (graphRelativeProjectiveEmbedding f) := by
  have : IsClosedImmersion (graphRelativeProjectiveEmbedding f ≫ pullback.snd _ _) := by
    rw [graphRelativeProjectiveEmbedding_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd _ _)

/-- The Chow line bundle is the actual pullback of the hyperplane bundle. -/
def graphLineBundle : (graphClosure f).Modules :=
  (Scheme.Modules.pullback (graphProjectiveImmersion f)).obj (O k (graphProjectiveDimension f) 1)

/-- The Chow line bundle has local rank one. -/
theorem graphLineBundle_locallyFreeRankOne : LocallyFreeRankOne (graphLineBundle f) :=
  (O_locallyFreeRankOne k (graphProjectiveDimension f) 1).pullback (graphProjectiveImmersion f)

/-- The absolute closed projective presentation of the Chow line bundle. -/
def graphLineBundlePresentation :
    VeryAmplePresentation (graphClosureπ f ≫ f) (graphLineBundle f) where
  dimension := graphProjectiveDimension f
  embedding := graphProjectiveImmersion f
  isClosedImmersion := inferInstance
  over := graphProjectiveImmersion_baseProjection f
  coefficientIso := Iso.refl _

/-- All natural tensor powers, including the structure module in degree zero. -/
def graphLineBundlePower (n : ℕ) : (graphClosure f).Modules := tensorPower (graphLineBundle f) n

/-- The zeroth power is definitionally the structure module. -/
@[simp]
lemma graphLineBundlePower_zero : graphLineBundlePower f 0 = structureModule (graphClosure f) := rfl

/-- The successor power is the actual sheaf tensor with the line bundle. -/
@[simp]
lemma graphLineBundlePower_succ (n : ℕ) : graphLineBundlePower f (n + 1) =
    ModuleSheafTensor.tensor (graphLineBundle f) (graphLineBundlePower f n) := rfl

/-- Every power has the absolute projective `O(n)` presentation. -/
def graphLineBundlePowerIso (n : ℕ) : graphLineBundlePower f n ≅
    (Scheme.Modules.pullback (graphProjectiveImmersion f)).obj
      (O k (graphProjectiveDimension f) (n : ℤ)) :=
  pullbackOOnePowerIso (graphProjectiveImmersion f) n

/-- The degree-zero presentation is the canonical structure-module pullback comparison. -/
@[simp]
lemma graphLineBundlePowerIso_zero :
    graphLineBundlePowerIso f 0 = (modulePullbackUnitIso (graphProjectiveImmersion f)).symm ≪≫
      (Scheme.Modules.pullback (graphProjectiveImmersion f)).mapIso
        (OZeroIso k (graphProjectiveDimension f)).symm := rfl

/-- The relative product presentation has exactly the same coefficients in every degree. -/
def graphRelativePowerIso (n : ℕ) : graphLineBundlePower f n ≅
    (Scheme.Modules.pullback (graphRelativeProjectiveEmbedding f)).obj
      ((Scheme.Modules.pullback (pullback.snd f
        (baseProjection k (Fin (graphProjectiveDimension f + 1))))).obj
          (O k (graphProjectiveDimension f) (n : ℤ))) :=
  graphLineBundlePowerIso f n ≪≫
    (Scheme.Modules.pullbackCongr (graphRelativeProjectiveEmbedding_snd f).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp (graphRelativeProjectiveEmbedding f)
      (pullback.snd _ _)).app _).symm

/-- The second presentation of the line bundle itself. -/
def graphRelativeLineBundleIso : graphLineBundle f ≅
    (Scheme.Modules.pullback (graphRelativeProjectiveEmbedding f)).obj
      ((Scheme.Modules.pullback (pullback.snd f
        (baseProjection k (Fin (graphProjectiveDimension f + 1))))).obj
          (O k (graphProjectiveDimension f) 1)) :=
  (Scheme.Modules.pullbackCongr (graphRelativeProjectiveEmbedding_snd f).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp (graphRelativeProjectiveEmbedding f)
      (pullback.snd _ _)).app _).symm

/-- Every power of the Chow bundle is locally free of rank one. -/
theorem graphLineBundlePower_locallyFreeRankOne (n : ℕ) :
    LocallyFreeRankOne (graphLineBundlePower f n) :=
  ((O_locallyFreeRankOne k (graphProjectiveDimension f) (n : ℤ)).pullback
    (graphProjectiveImmersion f)).of_iso (graphLineBundlePowerIso f n).symm

/-- The Chow bundle is relatively very ample for the modification. -/
theorem graphLineBundle_relativeVeryAmple :
    RelativeVeryAmple (graphClosureπ f) (graphLineBundle f) :=
  relativeVeryAmple_pullbackOOne (graphClosureπ f) f (graphProjectiveImmersion f)
    (graphProjectiveImmersion_baseProjection f)

/-- The same bundle is relatively very ample for the map to the field. -/
theorem graphLineBundle_absoluteVeryAmple :
    RelativeVeryAmple (graphClosureπ f ≫ f) (graphLineBundle f) :=
  relativeVeryAmple_pullbackOOne (graphClosureπ f ≫ f) (𝟙 _) (graphProjectiveImmersion f)
    (by simp [graphProjectiveImmersion_baseProjection])

/-- The explicit closed projective embedding over an affine open of the original source. -/
def graphLineBundleAffinePresentation (U : X.Opens) (hU : IsAffineOpen U) :
    VeryAmplePresentation ((graphClosureπ f ∣_ U) ≫ hU.isoSpec.hom)
      ((graphLineBundle f).restrict (graphClosureπ f ⁻¹ᵁ U).ι) :=
  targetAffinePresentation (graphClosureπ f) f (graphProjectiveImmersion f)
    (graphProjectiveImmersion_baseProjection f) U hU

/-- Coefficient transport for all powers over any target open, including power zero. -/
def graphLineBundleAffinePowerIso (U : X.Opens) (n : ℕ) :
    (graphLineBundlePower f n).restrict (graphClosureπ f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (targetOpenCoefficientMap (graphClosureπ f) f
        (graphProjectiveImmersion f) (graphProjectiveImmersion_baseProjection f) U)).obj
          (O Γ(X, U) (graphProjectiveDimension f) (n : ℤ)) :=
  targetOpenPowerIso (graphClosureπ f) f (graphProjectiveImmersion f)
    (graphProjectiveImmersion_baseProjection f) U n

/-- Restriction also identifies these coefficients with powers of the restricted line bundle. -/
def graphLineBundlePowerRestrictIso (U : X.Opens) (n : ℕ) :
    (graphLineBundlePower f n).restrict (graphClosureπ f ⁻¹ᵁ U).ι ≅
      tensorPower ((graphLineBundle f).restrict (graphClosureπ f ⁻¹ᵁ U).ι) n :=
  tensorPowerRestrictIso (graphLineBundle f) (graphClosureπ f ⁻¹ᵁ U).ι n

/-- The standard inverse-image charts of the affine-open projective presentation. -/
def graphAffineChart (U : X.Opens) (hU : IsAffineOpen U)
    (a : Fin (graphProjectiveDimension f + 1)) : (graphClosureπ f ⁻¹ᵁ U).toScheme.Opens :=
  (graphLineBundleAffinePresentation f U hU).embedding ⁻¹ᵁ chart Γ(X, U) _ a

/-- These finitely many opens are affine because the presentation is closed. -/
theorem graphAffineChart_isAffine (U : X.Opens) (hU : IsAffineOpen U)
    (a : Fin (graphProjectiveDimension f + 1)) : IsAffineOpen (graphAffineChart f U hU a) := by
  apply IsAffineOpen.preimage
  exact Proj.isAffineOpen_basicOpen (grading Γ(X, U) _) (MvPolynomial.X a)
    (MvPolynomial.isHomogeneous_X _ a) (by decide)

/-- The standard inverse-image affine charts cover the inverse image of the target open. -/
lemma iSup_graphAffineChart (U : X.Opens) (hU : IsAffineOpen U) :
    ⨆ a, graphAffineChart f U hU a = ⊤ := by
  change ⨆ a, (graphLineBundleAffinePresentation f U hU).embedding ⁻¹ᵁ
    chart Γ(X, U) (Fin (graphProjectiveDimension f + 1)) a = ⊤
  rw [← Scheme.Hom.preimage_iSup, iSup_chart]
  rfl

/-- The dense isomorphism open is nonempty when the source is nonempty. -/
theorem graphCommon_nonempty [Nonempty X] : ((chartData f).common : Set X).Nonempty :=
  (chartData f).common_dense.nonempty

/-- The actual generic point of an integral source belongs to the isomorphism open. -/
theorem graphCommon_genericPoint [IsIntegral X] : genericPoint X ∈ (chartData f).common :=
  (chartData f).common_contains_generics
    (by rw [genericPoints_eq_singleton]; exact Set.mem_singleton _)

/-- The inverse over the dense open commutes with the map to the original source. -/
@[reassoc]
lemma graphClosureCommonIso_inv_π :
    (graphClosureCommonIso f).inv ≫ (graphClosureπ f ⁻¹ᵁ (chartData f).common).ι ≫
      graphClosureπ f = (chartData f).common.ι := by
  rw [← graphClosureCommonIso_hom_ι, Iso.inv_hom_id_assoc]

/-- All geometry and both ampleness conclusions are outputs for a proper source. -/
theorem graphSimultaneousLineBundle_spec :
    IsProper (graphClosureπ f) ∧ Function.Surjective (graphClosureπ f) ∧
      Dense ((chartData f).common : Set X) ∧
      IsIso (graphClosureπ f ∣_ (chartData f).common) ∧
      IsClosedImmersion (graphProjectiveImmersion f) ∧
      IsClosedImmersion (graphRelativeProjectiveEmbedding f) ∧
      LocallyFreeRankOne (graphLineBundle f) ∧
      RelativeVeryAmple (graphClosureπ f) (graphLineBundle f) ∧
      RelativeVeryAmple (graphClosureπ f ≫ f) (graphLineBundle f) :=
  ⟨inferInstance, graphClosureπ_surjective f, (chartData f).common_dense, inferInstance,
    inferInstance, inferInstance, graphLineBundle_locallyFreeRankOne f,
    graphLineBundle_relativeVeryAmple f, graphLineBundle_absoluteVeryAmple f⟩

end FLT.Mazur.Chow
