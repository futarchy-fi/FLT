/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicModuliChart
public import FLT.Mazur.CyclicCharacteristicParameterPresheaf

/-!
# Smooth characteristic charts together with the actual integral degeneration

The three parameter choices retain the two existing normalized smooth families
and the genuine integral adic family. Each carries the full ample cyclic level.
No local coverage of arbitrary singular families or finite presentation is claimed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicAdicParameters
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CyclicCharacteristicAtlas
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The two normalized characteristic charts and the original complete-base chart. -/
def chart : Option Bool → Scheme
  | some b => normalizedLocus n b
  | none => OneGonAdicModuliChart.base

/-- Each choice retains its original full curve and actual ample cyclic subgroup. -/
def chartLevel : (b : Option Bool) → ampleCyclicLevels (chart n b) n
  | some b => ⟨⟨normalizedCurve n b, normalizedSubgroup n b⟩,
      normalizedSubgroup_isCyclic n b, normalizedSubgroup_isAmple n b⟩
  | none => OneGonAdicModuliChart.level n

/-- A test parameter remembers which of the three actual families it pulls back. -/
def Parameter (T : Scheme) := Σ b : Option Bool, ULift.{1} (T ⟶ chart n b)

/-- The parameter functor restricts the original scheme morphisms. -/
def parameterPresheaf : Schemeᵒᵖ ⥤ Type 1 where
  obj T := Parameter n T.unop
  map g := ↾(fun q ↦ ⟨q.1, ULift.up (g.unop ≫ q.2.down)⟩)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro q
    change (⟨q.1, ULift.up (𝟙 _ ≫ q.2.down)⟩ : Parameter n T.unop) = q
    rw [Category.id_comp, ULift.up_down]
    exact Sigma.eta q
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro q
    change (⟨q.1, ULift.up ((h.unop ≫ g.unop) ≫ q.2.down)⟩ : Parameter n _) =
      ⟨q.1, ULift.up (h.unop ≫ g.unop ≫ q.2.down)⟩
    rw [Category.assoc]

/-- The full original level on a parameter test. -/
def parameterLevel {T : Scheme} (q : Parameter n T) : ampleCyclicLevels T n :=
  ampleCyclicLevelsPullback q.2.down n (chartLevel n q.1)

/-- The modular class retains the whole original subgroup, including multiplicities. -/
def parameterClass {T : Scheme} (q : Parameter n T) : ampleCyclicClasses T n :=
  Quotient.mk _ (parameterLevel n q)

/-- Class formation commutes with every further test morphism. -/
theorem parameterClass_pullback {T U : Scheme} (g : U ⟶ T) (q : Parameter n T) :
    parameterClass n ((parameterPresheaf n).map g.op q) =
      ampleCyclicClassesPullback g n (parameterClass n q) :=
  congrFun (ampleCyclicClassesPullback_comp q.2.down g n) (Quotient.mk _ (chartLevel n q.1))

/-- The enlarged parameter functor maps naturally to the original modular presheaf. -/
def parameterModuliMap : parameterPresheaf n ⟶ ampleCyclicClassPresheaf n where
  app _ := ↾(parameterClass n)
  naturality _ _ g := by
    ext q
    exact parameterClass_pullback n g.unop q

/-- Include every original normalized smooth parameter with its marking unchanged. -/
def smoothInclusion : normalizedParameterPresheaf n ⟶ parameterPresheaf n where
  app _ := ↾(fun q ↦ ⟨some q.1, q.2⟩)
  naturality _ _ _ := rfl

/-- The inclusion preserves exactly the original smooth modular transformation. -/
theorem smoothInclusion_moduli :
    smoothInclusion n ≫ parameterModuliMap n = normalizedParameterModuliMap n := by
  ext T q
  exact (normalizedModuliMap_eq_pullback n q.1 q.2.down).symm

/-- Include all tests of the original nonconstant integral degeneration. -/
def adicInclusion : yoneda.obj OneGonAdicModuliChart.base ⋙ uliftFunctor.{1} ⟶
    parameterPresheaf n where
  app _ := ↾(fun q ↦ ⟨none, q⟩)
  naturality _ _ _ := rfl

/-- The adic inclusion retains the actual complete-base modular transformation. -/
theorem adicInclusion_moduli :
    adicInclusion n ≫ parameterModuliMap n = OneGonAdicModuliChart.moduliMap n := rfl

end FLT.Mazur.CyclicAdicParameters
