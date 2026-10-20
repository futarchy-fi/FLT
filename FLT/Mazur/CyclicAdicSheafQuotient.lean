/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicAdicParameterQuotient
public import FLT.Mazur.CyclicCharacteristicUnmarkedSheaf

/-!
# Fppf sheaf quotient of the actual smooth and adic parameters

Sheafification adds descent to the exact compatible-isomorphism quotient.
Its universal property uses invariance under all full mixed comparisons.
The smooth sheaf maps naturally into this enlargement. Scheme representation
and coverage of all generalized curves remain separate constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicAdicParameters
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The fppf sheaf quotient retaining all full compatible parameter comparisons. -/
def quotientSheaf : Sheaf Scheme.fppfTopology (Type 1) :=
  (presheafToSheaf Scheme.fppfTopology (Type 1)).obj (classPresheaf n)

/-- Map the actual full parameter classes to their sheafification. -/
def classToSheaf : classPresheaf n ⟶ (quotientSheaf n).obj :=
  toSheafify Scheme.fppfTopology (classPresheaf n)

/-- The canonical map from the original three-chart parameter functor. -/
def parameterToSheaf : parameterPresheaf n ⟶ (quotientSheaf n).obj :=
  projection n ≫ classToSheaf n

/-- The actual quotient projection is locally surjective. -/
instance projection_isLocallySurjective :
    Presheaf.IsLocallySurjective Scheme.fppfTopology (projection n) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (projection_surjective n)

/-- Original full compatible classes locally cover their sheafification. -/
instance classToSheaf_isLocallySurjective :
    Presheaf.IsLocallySurjective Scheme.fppfTopology (classToSheaf n) :=
  inferInstanceAs (Presheaf.IsLocallySurjective Scheme.fppfTopology (toSheafify _ _))

/-- Every section of the enlarged quotient sheaf locally has actual chart parameters. -/
instance parameterToSheaf_isLocallySurjective :
    Presheaf.IsLocallySurjective Scheme.fppfTopology (parameterToSheaf n) :=
  inferInstanceAs (Presheaf.IsLocallySurjective _ (projection n ≫ classToSheaf n))

variable {F : Sheaf Scheme.fppfTopology (Type 1)} (v : parameterPresheaf n ⟶ F.obj)

/-- A natural invariant respects full comparisons, including mixed smooth-adic comparisons. -/
def ParameterInvariant : Prop := ∀ (T : Scheme) (q r : Parameter n T),
  Related n q r → v.app (Opposite.op T) q = v.app (Opposite.op T) r

variable (hv : ParameterInvariant n v)

/-- Factor a full invariant through the exact pointwise compatible quotient. -/
def invariantClassMap : classPresheaf n ⟶ F.obj where
  app T := ↾(Quotient.lift (v.app T) (hv T.unop))
  naturality _ _ g := by
    ext q
    induction q using Quotient.inductionOn with | h q =>
      exact congrArg (fun k ↦ k q) (v.naturality g)

/-- Descend a full natural invariant to the constructed fppf quotient sheaf. -/
def sheafDesc : quotientSheaf n ⟶ F :=
  ⟨sheafifyLift Scheme.fppfTopology (invariantClassMap n v hv) F.property⟩

/-- Sheaf descent retains the prescribed values on every original parameter. -/
theorem parameterToSheaf_desc : parameterToSheaf n ≫ (sheafDesc n v hv).hom = v := by
  change (projection n ≫ toSheafify _ _) ≫ sheafifyLift _ _ _ = v
  rw [Category.assoc, toSheafify_sheafifyLift]
  rfl

/-- Actual parameters determine morphisms out of the enlarged sheaf uniquely. -/
theorem quotientSheaf_hom_ext {a b : quotientSheaf n ⟶ F}
    (h : parameterToSheaf n ≫ a.hom = parameterToSheaf n ≫ b.hom) : a = b := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext Scheme.fppfTopology _ _ F.property
  ext T z
  obtain ⟨q, rfl⟩ := projection_surjective n T z
  exact congrArg (fun k ↦ k.app T q) h

include hv in
/-- Full mixed comparison invariance gives a unique sheaf-valued factorization. -/
theorem sheafDesc_existsUnique :
    ∃! d : quotientSheaf n ⟶ F, parameterToSheaf n ≫ d.hom = v := by
  refine ⟨sheafDesc n v hv, parameterToSheaf_desc n v hv, ?_⟩
  intro d hd
  exact quotientSheaf_hom_ext n (hd.trans (parameterToSheaf_desc n v hv).symm)

/-- The existing normalized smooth quotient maps into the enlarged sheaf quotient. -/
def smoothSheafMap : CyclicCharacteristicAtlas.unmarkedParameterSheaf n ⟶ quotientSheaf n :=
  (presheafToSheaf Scheme.fppfTopology (Type 1)).map (smoothClassInclusion n)

/-- The smooth sheaf comparison retains the original full smooth quotient classes. -/
theorem smoothSheafMap_classes :
    CyclicCharacteristicAtlas.unmarkedClassToSheaf n ≫ (smoothSheafMap n).hom =
      smoothClassInclusion n ≫ classToSheaf n :=
  (toSheafify_naturality Scheme.fppfTopology (smoothClassInclusion n)).symm

end FLT.Mazur.CyclicAdicParameters
