/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedAcyclicOpenDivisor

/-!
# Open representation of the full unpointed Abel fibers over every test

For an arbitrary Picard-sheaf section on a test scheme, maps to its acyclic
open classify pairs consisting of a test map and an actual full divisor
representing the restricted section. The classification is natural and the
universal divisor is the constructed divisor on that open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- A test map together with an actual full divisor of the restricted original section. -/
def UnpointedAbelTestFiber (U : Over (Spec (.of R))) :=
  {z : (U ⟶ T) × AcyclicRankOneRelativeDivisor (Limits.pullback.snd f U.hom) //
    relativeFppfClass f U (abel _ z.2.val) = (relativeFppfSheaf f).obj.map z.1.op s}

/-- The explicit universal-divisor classification map for the actual open. -/
def unpointedAbelOpenFiberMap (U : Over (Spec (.of R)))
    (k : U ⟶ finiteTypeUnpointedFppfOpenTest f T s) : UnpointedAbelTestFiber f T s U :=
  ⟨⟨k ≫ finiteTypeUnpointedFppfOpenArrow f T s,
    finiteTypeAcyclicDivisorMap f k (finiteTypeUnpointedOpenDivisor f T s)⟩,
      finiteTypeUnpointedOpenDivisor_map_class f T s k⟩

/-- Maps to the open classify every full-divisor pair, including nonreduced test schemes. -/
def unpointedAbelOpenFiberEquiv (U : Over (Spec (.of R))) :
    (U ⟶ finiteTypeUnpointedFppfOpenTest f T s) ≃ UnpointedAbelTestFiber f T s U :=
  Equiv.ofBijective (unpointedAbelOpenFiberMap f T s U) ⟨by
    intro k l h
    apply Over.OverMorphism.ext
    apply (cancel_mono (finiteTypeUnpointedFppfAcyclicOpen f T s).ι).mp
    exact congrArg (fun z ↦ z.val.1.left) h, by
    rintro ⟨⟨b, D⟩, hD⟩
    have hm : (relativeFppfSheaf f).obj.map b.op s ∈
        (localGeometricAcyclicFppfSubfunctor f).obj (op U) := by
      rw [← hD]
      exact (localGeometricAcyclicFppf_class_iff f U _).mpr
        (finiteTypeTestAbel (IsPullback.of_hasPullback f U.hom) D).property
    obtain ⟨k, hk, _⟩ := (finiteTypeUnpointedFppfAcyclicOpen_represents_over f b s).mp hm
    refine ⟨k, Subtype.ext (Prod.ext hk ?_)⟩
    exact (finiteTypeUnpointedOpenDivisor_unique f T s k D (hk.symm ▸ hD)).symm⟩

/-- Restrict a full-divisor pair using the original test maps and full ideal comaps. -/
def unpointedAbelTestFiberMap {U V : Over (Spec (.of R))} (g : V ⟶ U)
    (z : UnpointedAbelTestFiber f T s U) : UnpointedAbelTestFiber f T s V := by
  refine ⟨⟨g ≫ z.val.1, finiteTypeAcyclicDivisorMap f g z.val.2⟩, ?_⟩
  rw [finiteTypeAcyclicDivisorMap_class, ← relativeFppfClass_naturality, z.property]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The actual test pairs form a presheaf with their original full-divisor restriction. -/
def unpointedAbelTestFiberPresheaf : (Over (Spec (.of R)))ᵒᵖ ⥤ Type where
  obj U := UnpointedAbelTestFiber f T s U.unop
  map g := ↾(unpointedAbelTestFiberMap f T s g.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact Prod.ext (Category.id_comp _) (finiteTypeAcyclicDivisorMap_id f U.unop z.val.2)
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact Prod.ext (Category.assoc _ _ _)
      (finiteTypeAcyclicDivisorMap_comp f h.unop g.unop z.val.2)

/-- The actual acyclic open represents the full Abel fiber over the supplied test section. -/
def unpointedAbelOpenFiberIso :
    yoneda.obj (finiteTypeUnpointedFppfOpenTest f T s) ≅
      unpointedAbelTestFiberPresheaf f T s :=
  NatIso.ofComponents (fun U ↦ (unpointedAbelOpenFiberEquiv f T s U.unop).toIso)
    (fun {U V} g ↦ by
      apply ConcreteCategory.hom_ext
      intro k
      apply Subtype.ext
      exact Prod.ext (Category.assoc _ _ _)
        (finiteTypeAcyclicDivisorMap_comp f g.unop k (finiteTypeUnpointedOpenDivisor f T s)))

/-- The represented map to the original test scheme is its actual open inclusion. -/
lemma unpointedAbelOpenFiberIso_base (U : Over (Spec (.of R)))
    (k : U ⟶ finiteTypeUnpointedFppfOpenTest f T s) :
    ((unpointedAbelOpenFiberIso f T s).hom.app (op U) k).val.1 =
      k ≫ finiteTypeUnpointedFppfOpenArrow f T s := rfl

/-- The universal family in this representation is the original full ideal comap. -/
lemma unpointedAbelOpenFiberIso_ideal (U : Over (Spec (.of R)))
    (k : U ⟶ finiteTypeUnpointedFppfOpenTest f T s) :
    ((unpointedAbelOpenFiberIso f T s).hom.app (op U) k).val.2.val.val =
      (finiteTypeUnpointedOpenDivisor f T s).val.val.comap (relativeTotalMap f k) :=
  finiteTypeAcyclicDivisorMap_ideal f k _

end FLT.Mazur.CartierAbel
