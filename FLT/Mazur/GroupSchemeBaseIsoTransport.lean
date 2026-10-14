/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupSchemeBaseChangeProjections

/-!
# Reindexing a group along a base isomorphism is its actual pullback

The comparison uses the inverse of the original fiber-product projection.
Its group upgrade follows from the Cartesian monoidal structures and retains
that exact projection on underlying schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GroupSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S T : Scheme.{u}} (e : S ≅ T)

/-- Reindexing along an inverse base isomorphism preserves the Cartesian structure. -/
abbrev baseIsoMapBraided : (Over.map e.inv).Braided := .ofChosenFiniteProducts _
attribute [local instance] baseIsoMapBraided

/-- The actual slice comparison is inverse to projection from the original fiber product. -/
def baseIsoOverComparison : Over.map e.inv ≅ Over.pullback e.hom :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (asIso (pullback.fst X.hom e.hom)).symm (by
    apply (cancel_mono e.hom).mp
    change (inv (pullback.fst X.hom e.hom) ≫ pullback.snd X.hom e.hom) ≫ e.hom =
      (X.hom ≫ e.inv) ≫ e.hom
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id])) (by
      intro X Y f
      apply Over.OverMorphism.ext
      apply (cancel_mono (pullback.fst Y.hom e.hom)).mp
      change (f.left ≫ inv (pullback.fst Y.hom e.hom)) ≫ _ =
        (inv (pullback.fst X.hom e.hom) ≫ ((Over.pullback e.hom).map f).left) ≫ _
      have hf : ((Over.pullback e.hom).map f).left ≫ pullback.fst Y.hom e.hom =
          pullback.fst X.hom e.hom ≫ f.left := pullback.lift_fst _ _ _
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc, hf,
        ← Category.assoc, IsIso.inv_hom_id, Category.id_comp])

/-- The two base transports agree as constructed commutative group schemes. -/
def baseIsoGroupComparison (G : CommGrp (Over T)) :
    (Over.map e.inv).mapCommGrp.obj G ≅ (Over.pullback e.hom).mapCommGrp.obj G :=
  (Functor.mapCommGrpNatIso (baseIsoOverComparison e)).app G

/-- The forward comparison projects to the unchanged underlying original scheme. -/
@[reassoc] theorem baseIsoGroupComparison_hom_fst (G : CommGrp (Over T)) :
    (baseIsoGroupComparison e G).hom.hom.hom.hom.left ≫ pullback.fst G.X.hom e.hom =
      𝟙 G.X.left := by
  change inv (pullback.fst G.X.hom e.hom) ≫ pullback.fst G.X.hom e.hom = _
  exact IsIso.inv_hom_id _

/-- The inverse is exactly the original fiber-product projection. -/
theorem baseIsoGroupComparison_inv (G : CommGrp (Over T)) :
    (baseIsoGroupComparison e G).inv.hom.hom.hom.left =
      pullback.fst G.X.hom e.hom := rfl

end FLT.Mazur.GroupSchemeBaseChange
