/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedRelation

/-!
# The parameter presheaf for both normalized characteristic charts

This is the presheaf coproduct of the two representable parameter functors.
A section retains its characteristic choice. The natural map to original
modular classes forgets that choice and the independent auxiliary markings.
Its exact pointwise kernel is the genuine unmarked comparison relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Parameters on a test scheme retain their actual characteristic chart. -/
def NormalizedParameter (T : Scheme) := Σ b : Bool, ULift.{1} (T ⟶ normalizedLocus n b)

/-- Both characteristic choices assemble into one contravariant parameter functor. -/
def normalizedParameterPresheaf : Schemeᵒᵖ ⥤ Type 1 where
  obj T := NormalizedParameter n T.unop
  map g := ↾(fun q ↦ ⟨q.1, ULift.up (g.unop ≫ q.2.down)⟩)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro q
    change (⟨q.1, ULift.up (𝟙 _ ≫ q.2.down)⟩ : NormalizedParameter n T.unop) = q
    rw [Category.id_comp, ULift.up_down]
    exact Sigma.eta q
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro q
    change (⟨q.1, ULift.up ((h.unop ≫ g.unop) ≫ q.2.down)⟩ :
      NormalizedParameter n _) = ⟨q.1, ULift.up (h.unop ≫ g.unop ≫ q.2.down)⟩
    rw [Category.assoc]

/-- The actual unmarked modular class of a parameter, in either characteristic chart. -/
def normalizedParameterClass {T : Scheme} (q : NormalizedParameter n T) :
    ampleCyclicClasses T n :=
  (normalizedModuliMap n q.1).app (Opposite.op T) q.2

/-- Forgetting a parameter's auxiliary choices commutes with arbitrary base change. -/
theorem normalizedParameterClass_pullback {T U : Scheme} (g : U ⟶ T)
    (q : NormalizedParameter n T) :
    normalizedParameterClass n ((normalizedParameterPresheaf n).map g.op q) =
      ampleCyclicClassesPullback g n (normalizedParameterClass n q) :=
  normalizedModuliMap_pullback n q.1 g q.2.down

/-- The single natural parameter-to-moduli map includes comparisons across characteristics. -/
def normalizedParameterModuliMap : normalizedParameterPresheaf n ⟶ ampleCyclicClassPresheaf n where
  app T := ↾(normalizedParameterClass n)
  naturality _ _ g := by
    ext q
    exact normalizedParameterClass_pullback n g.unop q

/-- The pointwise relation is defined by genuine full-curve/subgroup compatible isomorphisms. -/
def normalizedParameterSetoid (T : Scheme) : Setoid (NormalizedParameter n T) where
  r q r := UnmarkedRelated n q.1 r.1 q.2.down r.2.down
  iseqv := ⟨fun q ↦ unmarkedRelated_refl n q.1 q.2.down,
    fun h ↦ UnmarkedRelated.symm n h, fun h k ↦ UnmarkedRelated.trans n h k⟩

/-- Its equivalence classes are exactly the fibers of the original modular-class map. -/
theorem normalizedParameter_related_iff {T : Scheme} (q r : NormalizedParameter n T) :
    (normalizedParameterSetoid n T).r q r ↔
      normalizedParameterClass n q = normalizedParameterClass n r :=
  unmarkedRelated_iff_moduli_eq n q.1 r.1 q.2.down r.2.down

/-- Pullback preserves this actual relation with no restriction on the characteristic choices. -/
theorem normalizedParameter_pullback_related {T U : Scheme} (g : U ⟶ T)
    {q r : NormalizedParameter n T} (h : (normalizedParameterSetoid n T).r q r) :
    (normalizedParameterSetoid n U).r ((normalizedParameterPresheaf n).map g.op q)
      ((normalizedParameterPresheaf n).map g.op r) :=
  UnmarkedRelated.baseChange n h g

end FLT.Mazur.CyclicCharacteristicAtlas
