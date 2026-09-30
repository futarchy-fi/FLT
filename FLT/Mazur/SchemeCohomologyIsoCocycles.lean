/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCohomologyIso
public import FLT.Mazur.OpenDirectImageRestriction

/-!
# Cocycle computation for transport along a scheme isomorphism

The canonical constant-sheaf comparison preserves the represented global
section. Consequently the existing Ext equivalence transports section cocycles.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.SchemeCohomologyIso

open OpenSheafFreeComparison ExactFunctorInjectiveExt AbsoluteDirectImageCohomology

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- An isomorphism maps the top open to the top open. -/
lemma image_top : e.hom.opensFunctor.obj ⊤ = ⊤ := by
  rw [← Scheme.Hom.inv_preimage e]
  exact Opens.map_top _

/-- Evaluation of a restricted sheaf at top identifies with the original global sections. -/
def topIso (F : TopCat.Sheaf AddCommGrpCat.{u} Y) :
    ((abelianSheafEquivalence e).inverse.obj F).obj.obj (op ⊤) ≅ F.obj.obj (op ⊤) :=
  F.obj.mapIso (eqToIso (image_top e).symm).op

private lemma terminal_evaluation (F : TopCat.Sheaf AddCommGrpCat.{u} Y)
    {T : Y.Opens} (hT : IsTerminal T) (h : T = ⊤)
    (a : constantInteger Y ⟶ F) :
    (constantSheafAdj _ AddCommGrpCat.{u} hT).homEquiv _ F a ≫
        F.obj.map (eqToHom h.symm).op =
      (constantSheafAdj _ AddCommGrpCat.{u} isTerminalTop).homEquiv _ F a := by
  subst T
  have : hT = (isTerminalTop (α := Y.Opens)) := Subsingleton.elim _ _
  subst hT
  simp

/-- The adjoint of the canonical constant-integer comparison preserves evaluation. -/
lemma constantIntegerIso_evaluation (F : TopCat.Sheaf AddCommGrpCat.{u} Y)
    (a : constantInteger Y ⟶ F) :
    (topIso e F).hom
      (constantIntegerHomEquiv _ ((abelianSheafEquivalence e).toAdjunction.homEquiv _ _
        ((constantIntegerIso e).hom ≫ a))) = constantIntegerHomEquiv F a := by
  let adjX := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (isTerminalTop (α := X.Opens))
  let hT : IsTerminal (e.hom.opensFunctor.obj ⊤) := by
    rw [image_top e]
    exact isTerminalTop
  let adjY := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} hT
  have h := (adjX.comp (abelianSheafEquivalence e).toAdjunction).homEquiv_naturality_right
    ((constantIntegerIso e).hom) a
  have hc : (adjX.comp (abelianSheafEquivalence e).toAdjunction).homEquiv _ _
      ((constantIntegerIso e).hom) = adjY.unit.app _ :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
  rw [hc] at h
  have ht := terminal_evaluation F hT (image_top e) a
  rw [Adjunction.homEquiv_unit] at ht
  erw [← h] at ht
  exact congrArg (fun k ↦ k (ULift.up (1 : ℤ))) ht

local instance sheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :=
  HasExt.standard _

local instance topSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} T) := HasExt.standard _

/-- The existing Ext equivalence acts on a resolution cocycle by adjunction. -/
lemma sheafHEquiv_extMk {F : TopCat.Sheaf AddCommGrpCat.{u} Y}
    (I : InjectiveResolution F) {n : ℕ}
    (a : constantInteger Y ⟶ I.cocomplex.X n)
    (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    sheafHEquiv e F n (I.extMk a (n + 1) rfl ha) =
      (imageResolution (abelianSheafEquivalence e).inverse I).extMk
        ((abelianSheafEquivalence e).toAdjunction.homEquiv _ _
          ((constantIntegerIso e).hom ≫ a)) (n + 1) rfl (by
            rw [Adjunction.homEquiv_unit]
            change (_ ≫ (abelianSheafEquivalence e).inverse.map _) ≫
              (abelianSheafEquivalence e).inverse.map _ = 0
            rw [Category.assoc, ← Functor.map_comp, Category.assoc, ha,
              comp_zero, Functor.map_zero, comp_zero]) := by
  change (abelianSheafEquivalence e).toAdjunction.extEquiv
    ((Ext.mk₀ (constantIntegerIso e).hom).comp
      (I.extMk a (n + 1) rfl ha) (zero_add n)) = _
  rw [InjectiveResolution.mk₀_comp_extMk]
  exact extEquiv_extMk (abelianSheafEquivalence e).inverse I
    (abelianSheafEquivalence e).toAdjunction _ _

/-- Transport along a scheme isomorphism commutes with coefficient maps. -/
lemma sheafHEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} Y}
    (f : F ⟶ G) (n : ℕ) (x : Sheaf.H F n) :
    sheafHEquiv e G n (Sheaf.H.map f n x) =
      Sheaf.H.map ((abelianSheafEquivalence e).inverse.map f) n
        (sheafHEquiv e F n x) := by
  change (abelianSheafEquivalence e).toAdjunction.extEquiv
    ((Ext.mk₀ (constantIntegerIso e).hom).comp
      (x.comp (Ext.mk₀ f) (add_zero n)) (zero_add n)) = _
  rw [← Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)]
  exact Adjunction.extEquiv_naturality_right₀ (abelianSheafEquivalence e).toAdjunction _ f

/-- Transport global section cocycles through the canonical top-open identification. -/
def isoCycles {F : TopCat.Sheaf AddCommGrpCat.{u} Y}
    (I : InjectiveResolution F) (n : ℕ) :
    sectionCycles I n →+
      sectionCycles (imageResolution (abelianSheafEquivalence e).inverse I) n where
  toFun x := ⟨(topIso e (I.cocomplex.X n)).inv x.1, by
    change ((I.cocomplex.d n (n + 1)).hom.app _)
      ((I.cocomplex.X n).obj.map _ x.1) = 0
    erw [← ConcreteCategory.comp_apply, NatTrans.naturality,
      ConcreteCategory.comp_apply]
    change (I.cocomplex.X (n + 1)).obj.map _
      ((I.cocomplex.d n (n + 1)).hom.app (op ⊤) x.1) = 0
    rw [show (I.cocomplex.d n (n + 1)).hom.app (op ⊤) x.1 = 0 from x.2, map_zero]⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- The canonical scheme-isomorphism Ext comparison preserves section cocycles in all degrees. -/
lemma sheafHEquiv_sectionClass {F : TopCat.Sheaf AddCommGrpCat.{u} Y}
    (I : InjectiveResolution F) (n : ℕ) (x : sectionCycles I n) :
    sheafHEquiv e F n (sectionClass I n x) =
      sectionClass (imageResolution (abelianSheafEquivalence e).inverse I) n
        (isoCycles e I n x) := by
  change sheafHEquiv e F n (I.extMk _ _ rfl (sectionHom_d I n x)) = _
  refine (sheafHEquiv_extMk e I _ (sectionHom_d I n x)).trans ?_
  have h : (abelianSheafEquivalence e).toAdjunction.homEquiv _ _
      ((constantIntegerIso e).hom ≫ (sectionHomEquiv (I.cocomplex.X n)).symm x.1) =
      (sectionHomEquiv ((abelianSheafEquivalence e).inverse.obj (I.cocomplex.X n))).symm
        ((topIso e (I.cocomplex.X n)).inv x.1) := by
    apply (sectionHomEquiv ((abelianSheafEquivalence e).inverse.obj
      (I.cocomplex.X n))).injective
    apply (topIso e (I.cocomplex.X n)).addCommGroupIsoToAddEquiv.injective
    change (topIso e (I.cocomplex.X n)).hom (constantIntegerHomEquiv _ _) = _
    rw [constantIntegerIso_evaluation]
    erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact ((topIso e (I.cocomplex.X n)).addCommGroupIsoToAddEquiv.apply_symm_apply
      x.1).symm
  simp only [sectionClass, AddMonoidHom.coe_mk, h]
  rfl

end FLT.Mazur.SchemeCohomologyIso
