/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicAdicParameterRelation
public import FLT.Mazur.CyclicCharacteristicUnmarkedQuotientPresheaf

/-!
# The exact pointwise quotient of the enlarged parameter functor

The quotient uses all actual compatible comparisons, including mixed smooth
and adic comparisons. It embeds in the original ample cyclic class presheaf.
The existing smooth quotient embeds without identifying extra objects.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicAdicParameters
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Classes of the actual three-chart parameters under full compatible comparisons. -/
def ParameterClasses (T : Scheme) := Quotient (parameterSetoid n T)

/-- The actual original modular object represented by an enlarged parameter class. -/
def classMap (T : Scheme) : ParameterClasses n T → ampleCyclicClasses T n :=
  Quotient.lift (parameterClass n) (fun q r h ↦ (related_iff_class_eq n q r).mp h)

/-- The exact full relation identifies no additional original modular objects. -/
theorem classMap_injective (T : Scheme) : Function.Injective (classMap n T) := by
  intro q r
  induction q using Quotient.inductionOn with | h q =>
    induction r using Quotient.inductionOn with | h r =>
      intro h
      exact Quotient.sound ((related_iff_class_eq n q r).mpr h)

/-- Arbitrary scheme base change acts on full compatible parameter classes. -/
def classPresheaf : Schemeᵒᵖ ⥤ Type 1 where
  obj T := ParameterClasses n T.unop
  map g := ↾(Quotient.map ((parameterPresheaf n).map g)
    (fun _ _ h ↦ Related.baseChange n h g.unop))
  map_id T := by
    ext q
    induction q using Quotient.inductionOn with | h q =>
      change Quotient.mk _ ((parameterPresheaf n).map (𝟙 T) q) = Quotient.mk _ q
      rw [(parameterPresheaf n).map_id]
      rfl
  map_comp g h := by
    ext q
    induction q using Quotient.inductionOn with | h q =>
      change Quotient.mk _ ((parameterPresheaf n).map (g ≫ h) q) =
        Quotient.mk _ ((parameterPresheaf n).map h ((parameterPresheaf n).map g q))
      rw [(parameterPresheaf n).map_comp]
      rfl

/-- The original modular-class injection is natural on every scheme test. -/
def classModuliMap : classPresheaf n ⟶ ampleCyclicClassPresheaf n where
  app T := ↾(classMap n T.unop)
  naturality _ _ g := by
    ext q
    induction q using Quotient.inductionOn with | h q =>
      exact parameterClass_pullback n g.unop q

/-- Project each actual parameter to its full compatible class. -/
def projection : parameterPresheaf n ⟶ classPresheaf n where
  app _ := ↾(Quotient.mk _)
  naturality _ _ _ := rfl

/-- Each quotient section has an actual three-chart representative. -/
theorem projection_surjective (T : Schemeᵒᵖ) :
    Function.Surjective ((projection n).app T) := Quotient.mk_surjective

/-- Projection retains the complete original modular object. -/
theorem projection_moduli : projection n ≫ classModuliMap n = parameterModuliMap n := rfl

/-- The old smooth quotient embeds naturally in the enlarged quotient. -/
def smoothClassInclusion : CyclicCharacteristicAtlas.unmarkedParameterClassPresheaf n ⟶
    classPresheaf n where
  app T := ↾(Quotient.map ((smoothInclusion n).app T)
    (fun q r h ↦ (smooth_related_iff n q r).mpr h))
  naturality _ _ _ := by
    ext q
    induction q using Quotient.inductionOn with | h q => rfl

/-- The embedded smooth quotient retains its original modular transformation. -/
theorem smoothClassInclusion_moduli : smoothClassInclusion n ≫ classModuliMap n =
    CyclicCharacteristicAtlas.unmarkedParameterModuliMap n := by
  ext T q
  induction q using Quotient.inductionOn with | h q =>
    exact (CyclicCharacteristicAtlas.normalizedModuliMap_eq_pullback n q.1 q.2.down).symm

/-- Adding the adic family does not collapse any distinct smooth parameter classes. -/
theorem smoothClassInclusion_injective (T : Schemeᵒᵖ) :
    Function.Injective ((smoothClassInclusion n).app T) := by
  intro q r h
  apply CyclicCharacteristicAtlas.unmarkedParameterClassMap_injective n T.unop
  have hq := congrArg (fun k ↦ k.app T q) (smoothClassInclusion_moduli n)
  have hr := congrArg (fun k ↦ k.app T r) (smoothClassInclusion_moduli n)
  exact hq.symm.trans ((congrArg (classMap n T.unop) h).trans hr)

end FLT.Mazur.CyclicAdicParameters
