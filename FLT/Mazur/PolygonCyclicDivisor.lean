/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicInclusion
public import FLT.Mazur.PolygonActionSmooth
public import FLT.Mazur.PolygonDivisorCoproduct

/-!
# The all-one divisor as a closed cyclic subgroup

The actual all-one divisor is isomorphic over the base to the constant cyclic
group. Transport gives its commutative group structure. Its inclusion into
the split smooth group preserves multiplication and is a closed immersion;
composing with the smooth-open inclusion recovers the original divisor map.
-/

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.PolygonCyclicDivisor
open PolygonPinching PolygonBoundaryDivisor
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)
  (hn : 0 < n) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
local notation "S" => Spec (CommRingCat.of K)
local notation "D" => ConstantCyclicGroup.model S n
local notation "I" => ideal K n p (fun _ ↦ 1)

/-- The all-one divisor with its actual base morphism. -/
abbrev divisor : Over S := Over.mk ((I).subschemeι ≫ C.hom)

/-- Reindex the constant components by Fin n, retaining the chosen coproduct. -/
def indexIso : (∐ fun _ : Fin n ↦ S) ≅ (D).left :=
  Sigma.reindex (ZMod.finEquiv n).toEquiv (fun _ : ZMod n ↦ S) ≪≫
    asIso (sigmaComparison (Over.forget S) (fun _ : ZMod n ↦ 𝟙_ (Over S)))

/-- The reindexing sends a component to its residue-class label. -/
@[reassoc]
theorem component_indexIso (i : Fin n) :
    Sigma.ι _ i ≫ (indexIso K n).hom =
      (ConstantCyclicGroup.component S n (ZMod.finEquiv n i)).left := by
  simp only [indexIso, Iso.trans_hom, asIso_hom]
  exact (Sigma.ι_reindex_hom_assoc (ZMod.finEquiv n).toEquiv (fun _ : ZMod n ↦ S) i
    (sigmaComparison (Over.forget S) (fun _ : ZMod n ↦ 𝟙_ (Over S)))).trans
      (ι_comp_sigmaComparison (Over.forget S) (fun _ : ZMod n ↦ 𝟙_ (Over S)) _)

/-- The all-one divisor is the underlying constant cyclic scheme. -/
def schemeIso : (D).left ≅ (I).subscheme :=
  (indexIso K n).symm ≪≫ PolygonDivisorCoproduct.coproductIso K n p hn q h (fun _ ↦ 1)

/-- Each constant component is exactly its all-one marked section. -/
@[reassoc]
theorem component_schemeIso_ι (i : Fin n) :
    (ConstantCyclicGroup.component S n (ZMod.finEquiv n i)).left ≫
      (schemeIso K n p hn q h).hom ≫ (I).subschemeι =
        PolygonMarkedSections.sectionMap K n p 1 i := by
  rw [← component_indexIso K n i]
  simp [schemeIso, Category.assoc]

/-- The comparison is an isomorphism over the original field. -/
def overIso : D ≅ divisor K n p :=
  Over.isoMk (schemeIso K n p hn q h) (by
    apply (cancel_epi (indexIso K n).hom).mp
    apply Sigma.hom_ext
    intro i
    change Sigma.ι _ i ≫ (indexIso K n).hom ≫ (schemeIso K n p hn q h).hom ≫
      (I).subschemeι ≫ C.hom = Sigma.ι _ i ≫ (indexIso K n).hom ≫ (D).hom
    rw [component_indexIso_assoc, component_schemeIso_ι_assoc,
      PolygonMarkedSections.section_base, component_indexIso_assoc]
    exact (ConstantCyclicGroup.component S n (ZMod.finEquiv n i)).w.symm)


/-- Transport the proved cyclic group laws to the divisor itself. -/
abbrev grpObj : GrpObj (divisor K n p) := GrpObj.ofIso (overIso K n p hn q h)

/-- The transported divisor group is commutative. -/
abbrev commGrpObj : CommGrpObj (divisor K n p) where
  __ := grpObj K n p hn q h
  mul_comm := by
    change (β_ _ _).hom ≫
      ((overIso K n p hn q h).inv ⊗ₘ (overIso K n p hn q h).inv) ≫
        MonObj.mul ≫ (overIso K n p hn q h).hom = _
    rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]
    rfl

/-- Include the divisor group into the actual split smooth group. -/
def inclusion : divisor K n p ⟶ PolygonSplitGroup.model K n :=
  (overIso K n p hn q h).inv ≫ ConstantCyclicInclusion.inclusion K n

instance inclusion_isMonHom :
    letI := grpObj K n p hn q h
    IsMonHom (inclusion K n p hn q h) := by
  let := grpObj K n p hn q h
  dsimp only [inclusion]
  infer_instance

variable [LocallyOfFinitePresentation C.hom]

/-- The subgroup inclusion recovers the original closed divisor map. -/
@[reassoc]
theorem inclusion_smoothMap :
    (inclusion K n p hn q h).left ≫ (PolygonActionSmooth.smoothMap K n hn p q h).left =
      (I).subschemeι := by
  apply (cancel_epi (schemeIso K n p hn q h).hom).mp
  apply (cancel_epi (indexIso K n).hom).mp
  apply Sigma.hom_ext
  intro i
  rw [component_indexIso_assoc]
  change (ConstantCyclicGroup.component S n (ZMod.finEquiv n i)).left ≫
    (schemeIso K n p hn q h).hom ≫
    ((overIso K n p hn q h).inv.left ≫ (ConstantCyclicInclusion.inclusion K n).left) ≫
      (PolygonActionSmooth.smoothMap K n hn p q h).left = _
  have he : (schemeIso K n p hn q h).hom ≫ (overIso K n p hn q h).inv.left = 𝟙 _ :=
    congrArg Over.Hom.left (overIso K n p hn q h).hom_inv_id
  rw [Category.assoc, ← Category.assoc (schemeIso K n p hn q h).hom, he,
    Category.id_comp, component_indexIso_assoc, component_schemeIso_ι]
  change ((ConstantCyclicGroup.component S n (ZMod.finEquiv n i) ≫
    ConstantCyclicInclusion.inclusion K n) ≫
      PolygonActionSmooth.smoothMap K n hn p q h).left = _
  rw [ConstantCyclicInclusion.component_inclusion, Category.assoc,
    PolygonActionSmooth.component_smoothMap, RingEquiv.symm_apply_apply,
    Over.comp_left, ProjectiveLineActionSpecialization.identity_left]
  rfl

include h in
/-- The subgroup inclusion is a closed immersion. -/
theorem inclusion_closed : IsClosedImmersion (inclusion K n p hn q h).left := by
  have : IsOpenImmersion (PolygonActionSmooth.smoothMap K n hn p q h).left := by
    dsimp only [PolygonActionSmooth.smoothMap, PolygonActionSmooth.smoothι, Over.comp_left,
      Over.homMk_left]
    have : IsIso (smoothIso K n hn p q h).inv.left :=
      inferInstanceAs (IsIso ((Over.forget S).map (smoothIso K n hn p q h).inv))
    infer_instance
  have : IsClosedImmersion ((inclusion K n p hn q h).left ≫
      (PolygonActionSmooth.smoothMap K n hn p q h).left) := by
    rw [inclusion_smoothMap]
    infer_instance
  exact IsClosedImmersion.of_comp _ (PolygonActionSmooth.smoothMap K n hn p q h).left

end FLT.Mazur.PolygonCyclicDivisor
