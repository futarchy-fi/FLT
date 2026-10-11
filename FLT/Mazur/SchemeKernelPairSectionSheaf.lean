/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenSectionDescent

/-!
# The structure sheaf as compatible functions on a scheme kernel pair

The equalizer rings on target opens form a presheaf using the original source
restriction maps. Effective descent gives a natural isomorphism with the actual
target structure sheaf, and hence proves the compatible-function presheaf is a sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y P : Scheme.{u}} {g : Y ⟶ X} {a b : P ⟶ Y}
  (H : IsPullback a b g g)

/-- Compatible functions on the actual inverse image of a target open. -/
def compatibleOpenSections (W : X.Opens) : Subring Γ(Y, g ⁻¹ᵁ W) :=
  RingHom.eqLocus (a.app (g ⁻¹ᵁ W)).hom
    (b.appLE (g ⁻¹ᵁ W) (a ⁻¹ᵁ (g ⁻¹ᵁ W)) (kernelPair_preimage_open H W).le).hom

/-- Pullback sections satisfy the original relation on its common open domain. -/
theorem app_mem_compatibleOpenSections (W : X.Opens) (t : Γ(X, W)) :
    g.app W t ∈ compatibleOpenSections H W := by
  have hh : g.app W ≫ a.app (g ⁻¹ᵁ W) =
      g.app W ≫ b.appLE (g ⁻¹ᵁ W) (a ⁻¹ᵁ (g ⁻¹ᵁ W))
        (kernelPair_preimage_open H W).le := by
    rw [g.app_eq_appLE, a.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact H.w
  exact congrArg (fun k ↦ k t) hh

variable [Flat g] [Surjective g] [LocallyOfFinitePresentation g]

/-- The original target section ring is precisely the compatible source-section ring. -/
def compatibleOpenSectionsEquiv (W : X.Opens) : Γ(X, W) ≃+* compatibleOpenSections H W :=
  RingEquiv.ofBijective
    ((g.app W).hom.codRestrict _ (app_mem_compatibleOpenSections H W)) ⟨
      fun _ _ h ↦ app_injective W (congrArg Subtype.val h), fun s ↦ by
        obtain ⟨t, ht, _⟩ := app_existsUnique H W s.val s.property
        exact ⟨t, Subtype.ext ht⟩⟩

/-- Original source restriction maps preserve the kernel-pair equation. -/
theorem compatibleOpenSections_restrict {V W : X.Opens} (h : V ≤ W)
    (s : compatibleOpenSections H W) :
    Y.presheaf.map ((TopologicalSpace.Opens.map g.base).map (homOfLE h)).op s.val ∈
      compatibleOpenSections H V := by
  obtain ⟨t, rfl⟩ := (compatibleOpenSectionsEquiv H W).surjective s
  have hn := congrArg (fun k ↦ k t) (g.naturality (homOfLE h).op)
  exact hn ▸ app_mem_compatibleOpenSections H V
    (X.presheaf.map (homOfLE h).op t)

/-- Restriction on compatible sections uses the existing source structure sheaf. -/
def compatibleOpenSectionsMap {V W : X.Opens} (h : V ≤ W) :
    compatibleOpenSections H W →+* compatibleOpenSections H V :=
  ((Y.presheaf.map ((TopologicalSpace.Opens.map g.base).map (homOfLE h)).op).hom.comp
    (compatibleOpenSections H W).subtype).codRestrict _
      (compatibleOpenSections_restrict H h)

/-- The actual compatible-source-section presheaf. -/
def compatibleSectionPresheaf : X.carrier.Presheaf CommRingCat.{u} where
  obj W := .of (compatibleOpenSections H W.unop)
  map k := CommRingCat.ofHom (compatibleOpenSectionsMap H k.unop.le)
  map_id W := by
    ext s
    exact congrArg (fun k ↦ k s.val) (Y.presheaf.map_id (op (g ⁻¹ᵁ W.unop)))
  map_comp k l := by
    ext s
    exact congrArg (fun k ↦ k s.val)
      (Y.presheaf.map_comp
        ((TopologicalSpace.Opens.map g.base).map k.unop).op
        ((TopologicalSpace.Opens.map g.base).map l.unop).op)

/-- Effective regular-function descent respects all restriction maps. -/
def compatibleSectionPresheafIso : X.presheaf ≅ compatibleSectionPresheaf H :=
  NatIso.ofComponents
    (fun W ↦ (compatibleOpenSectionsEquiv H W.unop).toCommRingCatIso) (by
      intro W V k
      ext s
      apply Subtype.ext
      exact congrArg (fun k ↦ k s) (g.naturality k))

/-- The compatible-section presheaf satisfies the sheaf condition. -/
theorem compatibleSectionPresheaf_isSheaf :
    (compatibleSectionPresheaf H).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iso_iff (compatibleSectionPresheafIso H)).mp X.sheaf.property

end FLT.Mazur.SchemeEffectiveEpiSections
