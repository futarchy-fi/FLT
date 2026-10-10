/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeReducedRelativeHZero

/-!
# Base change of the actual relative H0 comparison

Degree-zero cohomology pullback is obtained from the canonical H0-to-sections
maps and the original morphism of fiber products. The proved comparison with
base functions commutes with this actual pullback, including nonflat maps
between reduced locally Noetherian bases.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FLT.Mazur.SchemeReducedHZeroBaseChange
open FCurve StructureDirectImage SchemeReducedRelativeBaseChange
open SchemeProperGeometricFiberSections
variable {X S T U : Scheme.{0}} (f : X ⟶ S)

/-- Pull back H0 by pulling back its canonical global function on the actual fiber product. -/
def pullbackMap (a : T ⟶ S) (b : U ⟶ S) (c : U ⟶ T) (hc : c ≫ a = b) :
    ModuleH (image (pullback.snd f a)) 0 →+ ModuleH (image (pullback.snd f b)) 0 :=
  (moduleH0Equiv (image (pullback.snd f b))).symm.toAddMonoidHom.comp
    ((baseMap f a b c hc).appTop.hom.toAddMonoidHom.comp
      (moduleH0Equiv (image (pullback.snd f a))).toAddMonoidHom)

/-- The H0 pullback retains the original function pullback under the section comparison. -/
lemma pullbackMap_sections (a : T ⟶ S) (b : U ⟶ S) (c : U ⟶ T) (hc : c ≫ a = b)
    (z : ModuleH (image (pullback.snd f a)) 0) :
    moduleH0Equiv (image (pullback.snd f b)) (pullbackMap f a b c hc z) =
      (baseMap f a b c hc).appTop (moduleH0Equiv (image (pullback.snd f a)) z) :=
  (moduleH0Equiv (image (pullback.snd f b))).apply_symm_apply _

/-- Identity base change induces the identity morphism of the original fiber product. -/
lemma baseMap_id (a : T ⟶ S) : baseMap f a a (𝟙 T) (Category.id_comp a) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp only [baseMap_fst, baseMap_snd, Category.id_comp,
    Category.comp_id]

/-- Actual H0 pullback along the identity base morphism is the identity. -/
lemma pullbackMap_id (a : T ⟶ S) (z : ModuleH (image (pullback.snd f a)) 0) :
    pullbackMap f a a (𝟙 T) (Category.id_comp a) z = z := by
  apply (moduleH0Equiv (image (pullback.snd f a))).injective
  rw [pullbackMap_sections, baseMap_id, Scheme.Hom.id_appTop, CommRingCat.id_apply]

/-- Successive maps of the actual fiber products equal the map of the composite base triangle. -/
lemma baseMap_comp {V : Scheme.{0}} (a : T ⟶ S) (b : U ⟶ S) (d : V ⟶ S)
    (c : U ⟶ T) (e : V ⟶ U) (hc : c ≫ a = b) (he : e ≫ b = d)
    (hcomp : (e ≫ c) ≫ a = d) :
    baseMap f b d e he ≫ baseMap f a b c hc = baseMap f a d (e ≫ c) hcomp := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseMap_fst]
  · rw [Category.assoc, baseMap_snd, ← Category.assoc, baseMap_snd,
      baseMap_snd, Category.assoc]

/-- H0 pullback respects composition of arbitrary base morphisms. -/
lemma pullbackMap_comp {V : Scheme.{0}} (a : T ⟶ S) (b : U ⟶ S) (d : V ⟶ S)
    (c : U ⟶ T) (e : V ⟶ U) (hc : c ≫ a = b) (he : e ≫ b = d)
    (hcomp : (e ≫ c) ≫ a = d) (z : ModuleH (image (pullback.snd f a)) 0) :
    pullbackMap f b d e he (pullbackMap f a b c hc z) =
      pullbackMap f a d (e ≫ c) hcomp z := by
  apply (moduleH0Equiv (image (pullback.snd f d))).injective
  simp only [pullbackMap_sections]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, baseMap_comp f a b d c e hc he hcomp]

variable (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
  [IsReduced T] [IsLocallyNoetherian T]

/-- Actual H0 of the structure direct image is the ring of functions on the changed base. -/
def h0Equiv (a : T ⟶ S) :
    Γ(T, ⊤) ≃ₗ[Γ(T, ⊤)] ModuleH (image (pullback.snd f a)) 0 :=
  SchemeReducedRelativeSections.h0Equiv (pullback.snd f a)
    (baseChangedSection f s hs a) (baseChangedSection_projection f s hs a)

/-- The H0 comparison retains the original structural pullback on global functions. -/
lemma h0Equiv_sections (a : T ⟶ S) (r : Γ(T, ⊤)) :
    moduleH0Equiv (image (pullback.snd f a)) (h0Equiv f s hs a r) =
      (pullback.snd f a).appTop r :=
  SchemeReducedRelativeSections.h0Equiv_sections _ _ _ r

variable [IsReduced U] [IsLocallyNoetherian U]

/-- The actual H0 comparison commutes with every map between the allowed bases. -/
lemma h0Equiv_naturality (a : T ⟶ S) (b : U ⟶ S) (c : U ⟶ T)
    (hc : c ≫ a = b) (r : Γ(T, ⊤)) :
    pullbackMap f a b c hc (h0Equiv f s hs a r) = h0Equiv f s hs b (c.appTop r) := by
  apply (moduleH0Equiv (image (pullback.snd f b))).injective
  rw [pullbackMap_sections, h0Equiv_sections, h0Equiv_sections]
  exact ConcreteCategory.congr_hom (sectionsIso_naturality f s hs a b c hc) r

end FLT.Mazur.SchemeReducedHZeroBaseChange
