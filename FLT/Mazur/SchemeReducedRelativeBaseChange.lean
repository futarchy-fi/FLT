/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeReducedStructureSheaf

/-!
# Relative constant functions after reduced base change

A flat family with geometrically reduced fibers has reduced total space over
each reduced locally Noetherian base. Thus the actual global and sheaf comparisons
exist after every such base change, even if the original base is nonreduced.
The global comparisons commute with arbitrary morphisms between these bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.SchemeReducedRelativeBaseChange
variable {X S T U : Scheme.{0}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
open SchemeProperGeometricFiberSections

/-- The original fiber products map along any commutative triangle of bases. -/
def baseMap (a : T ⟶ S) (b : U ⟶ S) (c : U ⟶ T) (hc : c ≫ a = b) :
    pullback f b ⟶ pullback f a :=
  pullback.lift (pullback.fst f b) (pullback.snd f b ≫ c)
    (by rw [Category.assoc, hc, pullback.condition])

/-- The induced map commutes with the original projection to the total space. -/
lemma baseMap_fst (a : T ⟶ S) (b : U ⟶ S) (c : U ⟶ T) (hc : c ≫ a = b) :
    baseMap f a b c hc ≫ pullback.fst f a = pullback.fst f b :=
  pullback.lift_fst _ _ _

/-- The induced map retains its specified base morphism. -/
lemma baseMap_snd (a : T ⟶ S) (b : U ⟶ S) (c : U ⟶ T) (hc : c ≫ a = b) :
    baseMap f a b c hc ≫ pullback.snd f a = pullback.snd f b ≫ c :=
  pullback.lift_snd _ _ _

variable [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
  [IsReduced T] [IsLocallyNoetherian T]

/-- The actual relative global-function comparison on every reduced Noetherian base change. -/
def sectionsIso (a : T ⟶ S) : Γ(T, ⊤) ≅ Γ(pullback f a, ⊤) :=
  SchemeReducedRelativeSections.sectionsIso (pullback.snd f a)
    (baseChangedSection f s hs a) (baseChangedSection_projection f s hs a)

/-- The comparison retains the original fiber-product projection. -/
lemma sectionsIso_hom (a : T ⟶ S) : (sectionsIso f s hs a).hom =
    (pullback.snd f a).appTop := rfl

/-- Its inverse is evaluation at the original base-changed section. -/
lemma sectionsIso_inv (a : T ⟶ S) : (sectionsIso f s hs a).inv =
    (baseChangedSection f s hs a).appTop := rfl

/-- The full structure-sheaf comparison exists after every reduced Noetherian base change. -/
def structureSheafIso (a : T ⟶ S) : T.sheaf ≅
    (TopCat.Sheaf.pushforward CommRingCat (pullback.snd f a).base).obj
      (pullback f a).sheaf :=
  SchemeReducedRelativeSections.structureSheafIso (pullback.snd f a)
    (baseChangedSection f s hs a) (baseChangedSection_projection f s hs a)

/-- The sheaf comparison retains the original structural morphism on every open. -/
lemma structureSheafIso_hom_app (a : T ⟶ S) (V : T.Opens) :
    (structureSheafIso f s hs a).hom.hom.app (.op V) = (pullback.snd f a).app V := rfl

variable [IsReduced U] [IsLocallyNoetherian U]

/-- These comparisons commute with every morphism between the allowed bases. -/
lemma sectionsIso_naturality (a : T ⟶ S) (b : U ⟶ S) (c : U ⟶ T)
    (hc : c ≫ a = b) :
    (sectionsIso f s hs a).hom ≫ (baseMap f a b c hc).appTop =
      c.appTop ≫ (sectionsIso f s hs b).hom := by
  change (pullback.snd f a).appTop ≫ (baseMap f a b c hc).appTop =
    c.appTop ≫ (pullback.snd f b).appTop
  rw [← Scheme.Hom.comp_appTop, baseMap_snd, Scheme.Hom.comp_appTop]

/-- Evaluation along the sections is compatible with the same base morphisms. -/
lemma sectionsIso_inv_naturality (a : T ⟶ S) (b : U ⟶ S) (c : U ⟶ T)
    (hc : c ≫ a = b) :
    (baseMap f a b c hc).appTop ≫ (sectionsIso f s hs b).inv =
      (sectionsIso f s hs a).inv ≫ c.appTop := by
  rw [← cancel_epi (sectionsIso f s hs a).hom, ← Category.assoc,
    sectionsIso_naturality f s hs a b c hc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end FLT.Mazur.SchemeReducedRelativeBaseChange
