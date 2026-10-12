/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicHilbertFixedBasePicard
public import FLT.Mazur.VariableTranslatedHilbertChart

/-!
# Fixed-base comparison for genuinely varying translation coordinates

The translation base may be restricted independently. Its actual coordinate
is retained, and the whole translated class is transported and reflected.
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

/-- Restrict the original translation section along its actual base morphism. -/
def fixedBaseTranslationClass : (relativeFppfSheaf q).obj.obj (op W) :=
  (relativeFppfBaseChange f a).hom.hom.app (op W) ((relativeFppfSheaf f).obj.map t.op c)

omit [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f] in
/-- The translated class is natural along the independent translation coordinate. -/
theorem fixedBaseTranslationClass_map {T : Over (Spec (.of R'))} (b : T ⟶ W) :
    (relativeFppfSheaf q).obj.map b.op (fixedBaseTranslationClass f a V W t c) =
      (relativeFppfBaseChange f a).hom.hom.app (op T)
        ((relativeFppfSheaf f).obj.map ((Over.map a).map b ≫ t).op c) := by
  have h := congrArg (fun u ↦ u ((relativeFppfSheaf f).obj.map t.op c))
    ((relativeFppfBaseChange f a).hom.hom.naturality b.op)
  change (relativeFppfBaseChange f a).hom.hom.app (op T)
      ((relativeFppfSheaf f).obj.map ((Over.map a).map b).op
        ((relativeFppfSheaf f).obj.map t.op c)) =
    (relativeFppfSheaf q).obj.map b.op (fixedBaseTranslationClass f a V W t c) at h
  simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using h.symm

/-- The actual varying chart preserves the original translated Picard map. -/
theorem variableHilbertFixedBase_picard (T : Over (Spec (.of R')))
    (k : (Over.map a).obj T ⟶ variableHilbertTest f d V) (b : T ⟶ W)
    (hb : (Over.map a).map b ≫ t = k ≫ variableHilbertBase f d V) :
    variableHilbertPoint q d (fixedBaseAmple f a hL) W
        (fixedBaseTranslationClass f a V W t c) T
        (variableHilbertLift q d W b
          (acyclicHilbertFixedBaseParameter f a hL d T (k ≫ variableHilbertParameter f d V))) =
      (relativeFppfBaseChange f a).hom.hom.app (op T)
        (variableHilbertPoint f d hL V c ((Over.map a).obj T) k) := by
  rw [variableHilbertPoint_lift, acyclicHilbertFixedBaseParameter_picard,
    fixedBaseTranslationClass_map, hb]
  exact (map_div _ _ _).symm

/-- Equality of translated original classes is reflected even for distinct base coordinates. -/
theorem variableHilbertFixedBase_eq_iff (T : Over (Spec (.of R')))
    (k l : (Over.map a).obj T ⟶ variableHilbertTest f d V) (b e : T ⟶ W)
    (hb : (Over.map a).map b ≫ t = k ≫ variableHilbertBase f d V)
    (he : (Over.map a).map e ≫ t = l ≫ variableHilbertBase f d V) :
    variableHilbertPoint q d (fixedBaseAmple f a hL) W
        (fixedBaseTranslationClass f a V W t c) T
        (variableHilbertLift q d W b
          (acyclicHilbertFixedBaseParameter f a hL d T (k ≫ variableHilbertParameter f d V))) =
      variableHilbertPoint q d (fixedBaseAmple f a hL) W
        (fixedBaseTranslationClass f a V W t c) T
        (variableHilbertLift q d W e
          (acyclicHilbertFixedBaseParameter f a hL d T (l ≫ variableHilbertParameter f d V))) ↔
      variableHilbertPoint f d hL V c ((Over.map a).obj T) k =
        variableHilbertPoint f d hL V c ((Over.map a).obj T) l := by
  rw [variableHilbertFixedBase_picard f a hL d V W t c T k b hb,
    variableHilbertFixedBase_picard f a hL d V W t c T l e he]
  let e := ((sheafToPresheaf _ _).mapIso (relativeFppfBaseChange f a)).app (op T)
  change e.hom _ = e.hom _ ↔ _
  constructor
  · intro h
    have hh := congrArg (fun z ↦ e.inv z) h
    simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply] using hh
  · exact congrArg _

end FLT.Mazur.HilbertChart
