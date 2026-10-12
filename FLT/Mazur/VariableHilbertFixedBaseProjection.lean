/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicHilbertFixedBaseProjection
public import FLT.Mazur.VariableHilbertFixedBasePicard

/-!
# Actual morphisms comparing varying Hilbert charts across coefficient bases

The comparison retains the map to the original translation base and the
entire Hilbert family. Its translated Picard equation is proved on every test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => Limits.pullback.snd f a
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The actual local chart maps to the original chart, preserving both coordinates. -/
def variableHilbertFixedBaseProjection :
    (Over.map a).obj (variableHilbertTest q d W) ⟶ variableHilbertTest f d V :=
  variableHilbertLift f d V ((Over.map a).map (variableHilbertBase q d W) ≫ t)
    ((Over.map a).map (variableHilbertParameter q d W) ≫
      acyclicHilbertFixedBaseProjection f a hL d)

/-- The projection keeps the independently varying original translation coordinate. -/
@[reassoc]
theorem variableHilbertFixedBaseProjection_base :
    variableHilbertFixedBaseProjection f a hL d V W t ≫ variableHilbertBase f d V =
      (Over.map a).map (variableHilbertBase q d W) ≫ t := prod.lift_fst _ _

/-- The projection keeps the actual original Hilbert parameter. -/
@[reassoc]
theorem variableHilbertFixedBaseProjection_hilbert :
    variableHilbertFixedBaseProjection f a hL d V W t ≫ variableHilbertParameter f d V =
      (Over.map a).map (variableHilbertParameter q d W) ≫
        acyclicHilbertFixedBaseProjection f a hL d := prod.lift_snd _ _

/-- The scheme comparison commutes with the full translated Picard map. -/
theorem variableHilbertFixedBaseProjection_picard (T : Over (Spec (.of R')))
    (k : T ⟶ variableHilbertTest q d W) :
    (relativeFppfBaseChange f a).hom.hom.app (op T)
        (variableHilbertPoint f d hL V c ((Over.map a).obj T)
          ((Over.map a).map k ≫ variableHilbertFixedBaseProjection f a hL d V W t)) =
      variableHilbertPoint q d (fixedBaseAmple f a hL) W
        (fixedBaseTranslationClass f a V W t c) T k := by
  simp only [variableHilbertPoint, Category.assoc,
    variableHilbertFixedBaseProjection_base, variableHilbertFixedBaseProjection_hilbert,
    map_div, ← fixedBaseTranslationClass_map, ← Functor.map_comp_assoc]
  rw [acyclicHilbertFixedBaseProjection_picard]

/-- The actual projection preserves and reflects the original full equal-class relation. -/
theorem variableHilbertFixedBaseProjection_eq_iff (T : Over (Spec (.of R')))
    (k l : T ⟶ variableHilbertTest q d W) :
    variableHilbertPoint f d hL V c ((Over.map a).obj T)
        ((Over.map a).map k ≫ variableHilbertFixedBaseProjection f a hL d V W t) =
      variableHilbertPoint f d hL V c ((Over.map a).obj T)
        ((Over.map a).map l ≫ variableHilbertFixedBaseProjection f a hL d V W t) ↔
      variableHilbertPoint q d (fixedBaseAmple f a hL) W
          (fixedBaseTranslationClass f a V W t c) T k =
        variableHilbertPoint q d (fixedBaseAmple f a hL) W
          (fixedBaseTranslationClass f a V W t c) T l := by
  let e := ((sheafToPresheaf _ _).mapIso (relativeFppfBaseChange f a)).app (op T)
  constructor
  · intro h
    have hh := congrArg ((relativeFppfBaseChange f a).hom.hom.app (op T)) h
    simpa only [variableHilbertFixedBaseProjection_picard] using hh
  · intro h
    rw [← variableHilbertFixedBaseProjection_picard f a hL d V W t c T k,
      ← variableHilbertFixedBaseProjection_picard f a hL d V W t c T l] at h
    change e.hom _ = e.hom _ at h
    have hh := congrArg (fun z ↦ e.inv z) h
    simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply] using hh

end FLT.Mazur.HilbertChart
