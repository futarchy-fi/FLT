/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationOperations
public import FLT.Mazur.SchemeRelationOverRestriction

/-!
# Nested restrictions of the full original Hilbert relation

Restricting an already restricted source gives the actual full two-endpoint
pullback of its original relation. The comparison preserves the relation arrow
and its independent-coordinate envelope map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
variable {B : Over (Spec (.of R))} (v : B ⟶ A)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "r" => fst f hL d V c (v ≫ k)
local notation "s" => snd f hL d V c (v ≫ k)

/-- Forgetting the source restriction retains the actual original full relation arrow. -/
def nestedToFullRelation : relation f hL d V c (v ≫ k) ⟶ relation f hL d V c k :=
  arrow f hL d V c k (r ≫ v) (s ≫ v) (by
    simpa only [sectionAt, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      equal_class f hL d V c (v ≫ k))

@[reassoc]
theorem nestedToFullRelation_fst : nestedToFullRelation f hL d V c k v ≫ p = r ≫ v :=
  arrow_fst f hL d V c k _ _ _

@[reassoc]
theorem nestedToFullRelation_snd : nestedToFullRelation f hL d V c k v ≫ q = s ≫ v :=
  arrow_snd f hL d V c k _ _ _

/-- Restrict the first endpoint of the unchanged original relation. -/
def nestedFullFirstRestriction : Over (Spec (.of R)) := pullback p v

/-- Restrict the second endpoint after the first, retaining the original relation scheme. -/
def nestedFullDoubleRestriction : Over (Spec (.of R)) := pullback (pullback.fst p v ≫ q) v

/-- The full two-endpoint restriction remembers its first source coordinate. -/
def nestedFullDoubleFst : nestedFullDoubleRestriction f hL d V c k v ⟶ B :=
  pullback.fst (pullback.fst p v ≫ q) v ≫ pullback.snd p v

/-- Its second source coordinate is independent of the first one. -/
def nestedFullDoubleSnd : nestedFullDoubleRestriction f hL d V c k v ⟶ B :=
  pullback.snd (pullback.fst p v ≫ q) v

/-- The unchanged original arrow underlying the double restriction. -/
def nestedFullDoubleArrow : nestedFullDoubleRestriction f hL d V c k v ⟶
    relation f hL d V c k :=
  pullback.fst (pullback.fst p v ≫ q) v ≫ pullback.fst p v

@[reassoc]
theorem nestedFullDoubleArrow_fst : nestedFullDoubleArrow f hL d V c k v ≫ p =
    nestedFullDoubleFst f hL d V c k v ≫ v := by
  simp only [nestedFullDoubleArrow, nestedFullDoubleFst, Category.assoc, pullback.condition]

@[reassoc]
theorem nestedFullDoubleArrow_snd : nestedFullDoubleArrow f hL d V c k v ≫ q =
    nestedFullDoubleSnd f hL d V c k v ≫ v := by
  exact pullback.condition (f := pullback.fst p v ≫ q) (g := v)

/-- An original arrow with lifted endpoints determines the restricted equal-class arrow. -/
def nestedFromFullDouble : nestedFullDoubleRestriction f hL d V c k v ⟶
    relation f hL d V c (v ≫ k) :=
  arrow f hL d V c (v ≫ k) (nestedFullDoubleFst f hL d V c k v)
    (nestedFullDoubleSnd f hL d V c k v) (by
    have h := congrArg ((relativeFppfSheaf f).obj.map (nestedFullDoubleArrow f hL d V c k v).op)
      (equal_class f hL d V c k)
    simpa only [sectionAt, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      nestedFullDoubleArrow_fst_assoc, nestedFullDoubleArrow_snd_assoc] using h)

@[reassoc]
theorem nestedFromFullDouble_fst : nestedFromFullDouble f hL d V c k v ≫ r =
    nestedFullDoubleFst f hL d V c k v := arrow_fst f hL d V c (v ≫ k) _ _ _

@[reassoc]
theorem nestedFromFullDouble_snd : nestedFromFullDouble f hL d V c k v ≫ s =
    nestedFullDoubleSnd f hL d V c k v := arrow_snd f hL d V c (v ≫ k) _ _ _

/-- The restricted relation maps to the actual two-endpoint pullback. -/
def nestedToFullDouble : relation f hL d V c (v ≫ k) ⟶ nestedFullDoubleRestriction f hL d V c k v :=
  pullback.lift (pullback.lift (nestedToFullRelation f hL d V c k v) r
    (nestedToFullRelation_fst f hL d V c k v)) s (by
      rw [pullback.lift_fst_assoc, nestedToFullRelation_snd])

@[reassoc]
theorem nestedToFullDouble_fst : nestedToFullDouble f hL d V c k v ≫
    nestedFullDoubleFst f hL d V c k v = r := by
  simp only [nestedToFullDouble, nestedFullDoubleFst, pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc]
theorem nestedToFullDouble_snd : nestedToFullDouble f hL d V c k v ≫
    nestedFullDoubleSnd f hL d V c k v = s :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem nestedFromFullDouble_original : nestedFromFullDouble f hL d V c k v ≫
    nestedToFullRelation f hL d V c k v = nestedFullDoubleArrow f hL d V c k v := by
  apply hom_ext f hL d V c k
  · rw [Category.assoc, nestedToFullRelation_fst, ← Category.assoc,
      nestedFromFullDouble_fst, nestedFullDoubleArrow_fst]
  · rw [Category.assoc, nestedToFullRelation_snd, ← Category.assoc,
      nestedFromFullDouble_snd, nestedFullDoubleArrow_snd]

/-- The equal-class relation is exactly the original full relation restricted at both endpoints. -/
def nestedFullDoubleIso : relation f hL d V c (v ≫ k) ≅
    nestedFullDoubleRestriction f hL d V c k v where
  hom := nestedToFullDouble f hL d V c k v
  inv := nestedFromFullDouble f hL d V c k v
  hom_inv_id := by
    apply hom_ext f hL d V c (v ≫ k)
    · rw [Category.assoc, nestedFromFullDouble_fst, nestedToFullDouble_fst, Category.id_comp]
    · rw [Category.assoc, nestedFromFullDouble_snd, nestedToFullDouble_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [nestedToFullDouble, Category.assoc, pullback.lift_fst, Category.id_comp]
        exact nestedFromFullDouble_original f hL d V c k v
      · simp only [nestedToFullDouble, Category.assoc, pullback.lift_fst_assoc,
          pullback.lift_snd, Category.id_comp]
        exact nestedFromFullDouble_fst f hL d V c k v
    · simp only [nestedToFullDouble, Category.assoc, pullback.lift_snd, Category.id_comp]
      exact nestedFromFullDouble_snd f hL d V c k v


/-- The nested full relation in the actual scheme double-pullback coordinates. -/
def nestedSchemeDoubleIso : (relation f hL d V c (v ≫ k)).left ≅
    SchemeRelationRestriction.doubleDomain (p).left (q).left v.left :=
  (Over.forget _).mapIso (nestedFullDoubleIso f hL d V c k v) ≪≫
    SchemeRelationRestriction.overDoubleIso p q v

/-- The nested scheme isomorphism retains the original relation arrow. -/
@[reassoc]
theorem nestedSchemeDoubleIso_arrow : (nestedSchemeDoubleIso f hL d V c k v).hom ≫
    SchemeRelationRestriction.arrow (p).left (q).left v.left =
      (nestedToFullRelation f hL d V c k v).left := by
  dsimp only [nestedSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_arrow]
  change (nestedToFullDouble f hL d V c k v ≫ nestedFullDoubleArrow f hL d V c k v).left = _
  simp only [nestedToFullDouble, nestedFullDoubleArrow,
    pullback.lift_fst_assoc, pullback.lift_fst]

/-- The nested relation comparison keeps the original independent-coordinate envelope. -/
theorem nestedToFullRelation_envelope :
    nestedToFullRelation f hL d V c k v ≫ toEnvelope f hL d V c k =
      toEnvelope f hL d V c (v ≫ k) ≫ prod.map v (𝟙 V) := by
  apply prod.hom_ext
  · simp only [Category.assoc, toEnvelope_test, prod.map_fst,
      nestedToFullRelation_snd, toEnvelope_test_assoc]
  · simp only [Category.assoc, toEnvelope_base, prod.map_snd, Category.comp_id,
      nestedToFullRelation_fst_assoc]

end FLT.Mazur.HilbertChart.AffineRestriction
