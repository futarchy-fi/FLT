/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RigidifiedPicardPullback
public import FLT.Mazur.PointedPicardKernelPresheaf

/-!
# Rigidified Picard classes as a presheaf

Restriction pulls back the actual bundles and their trivializations. The
kernel equivalence proves the functor laws and is natural for these maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- Restriction of rigidified classes over the original pointed fiber products. -/
def rigidifiedBaseMap {T U : Over S} (g : T ⟶ U) :
    RigidifiedPic (pointedBaseSection f e he U) →
      RigidifiedPic (pointedBaseSection f e he T) :=
  rigidifiedPicPullback _ _ (relativeTotalMap f g) g.left
    (pointedBaseSection_naturality f e he g)

/-- The restriction on rigidified classes corresponds to the actual kernel map. -/
theorem rigidifiedBaseMap_kernel {T U : Over S} (g : T ⟶ U)
    (a : RigidifiedPic (pointedBaseSection f e he U)) :
    rigidifiedKernel (pointedBaseSection f e he T) (rigidifiedBaseMap f e he g a) =
      pointedKernelMap f e he g (rigidifiedKernel (pointedBaseSection f e he U) a) := by
  apply Subtype.ext
  exact rigidifiedPicPullback_kernel _ _ _ _ _ a

/-- The presheaf of actual rigidified isomorphism classes. -/
def rigidifiedPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := RigidifiedPic (pointedBaseSection f e he T.unop)
  map g := ↾(rigidifiedBaseMap f e he g.unop)
  map_id T := by
    ext a
    apply rigidifiedKernel_injective _ (Limits.pullback.snd f T.unop.hom)
      (pointedBaseSection_snd f e he T.unop)
    apply Subtype.ext
    change (rigidifiedKernel _ (rigidifiedBaseMap f e he (𝟙 T.unop) a)).val = _
    rw [rigidifiedBaseMap_kernel, pointedKernelMap_val, relativeTotalMap_id, pullback_id]
    rfl
  map_comp {T U V} g h := by
    ext a
    apply rigidifiedKernel_injective _ (Limits.pullback.snd f V.unop.hom)
      (pointedBaseSection_snd f e he V.unop)
    apply Subtype.ext
    change (rigidifiedKernel _ (rigidifiedBaseMap f e he (g ≫ h).unop a)).val =
      (rigidifiedKernel _ (rigidifiedBaseMap f e he h.unop
        (rigidifiedBaseMap f e he g.unop a))).val
    rw [rigidifiedBaseMap_kernel, rigidifiedBaseMap_kernel, rigidifiedBaseMap_kernel]
    simp only [pointedKernelMap_val, unop_comp, relativeTotalMap_comp, pullback_comp]

/-- The actual rigidified-class presheaf identifies naturally with the normalized kernel. -/
def rigidifiedPresheafKernelIso :
    rigidifiedPresheaf f e he ≅ pointedKernelPresheaf f e he ⋙ forget CommGrpCat :=
  NatIso.ofComponents (fun T ↦
    (rigidifiedKernelEquiv (pointedBaseSection f e he T.unop)
      (Limits.pullback.snd f T.unop.hom) (pointedBaseSection_snd f e he T.unop)).toIso)
    (fun {T U} g ↦ by
      ext a
      exact rigidifiedBaseMap_kernel f e he g.unop a)

/-- The natural comparison sends the given rigidified bundle to its original class. -/
theorem rigidifiedPresheafKernelIso_mk (T : Over S)
    (L : RigidifiedBundle (pointedBaseSection f e he T)) :
    ((rigidifiedPresheafKernelIso f e he).hom.app (op T) (Quotient.mk _ L)).val =
      mk L.1.val L.1.property := rfl

end FLT.Mazur.SchemePicard
