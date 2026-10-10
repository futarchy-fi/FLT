/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasicoherentImageIdeal

/-!
# Full image ideals classify embeddings into the structure sheaf

Equality of the actual affine ideals is equivalent to an isomorphism of
embedded quasi-coherent sheaves preserving their inclusions. Such an
isomorphism is unique. These statements compare full ideals, not supports.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  (a : M ⟶ structureModule X) (b : N ⟶ structureModule X)

/-- Changing the source by an actual isomorphism preserves the full image ideal. -/
theorem quasicoherentImageIdeal_eq_of_iso (e : M ≅ N) (he : e.hom ≫ b = a) :
    quasicoherentImageIdeal a = quasicoherentImageIdeal b := by
  apply Scheme.IdealSheafData.ext
  funext U
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    refine ⟨e.hom.app U.1 s, ?_⟩
    exact congrArg (fun f ↦ f.app U.1 s) he
  · rintro _ ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app U.1)).surjective t
    exact ⟨s, (congrArg (fun f ↦ f.app U.1 s) he).symm⟩

/-- Equality of full image ideals constructs the unique compatible isomorphism. -/
def imageIdealEqualityIso [Mono a] [Mono b]
    (h : quasicoherentImageIdeal a = quasicoherentImageIdeal b) : M ≅ N :=
  GlobalIdealPowerCompatibility.affineImageIso a b (fun U ↦
    congrArg (fun I : X.IdealSheafData ↦ I.ideal U) h)

/-- The comparison preserves the actual maps into the structure sheaf. -/
@[reassoc (attr := simp)]
lemma imageIdealEqualityIso_comp [Mono a] [Mono b]
    (h : quasicoherentImageIdeal a = quasicoherentImageIdeal b) :
    (imageIdealEqualityIso a b h).hom ≫ b = a :=
  GlobalIdealPowerCompatibility.affineImageIso_comp _ _ _

/-- Full image ideals classify embeddings, with no chosen chart coordinates. -/
theorem quasicoherentImageIdeal_eq_iff_iso [Mono a] [Mono b] :
    quasicoherentImageIdeal a = quasicoherentImageIdeal b ↔
      ∃ e : M ≅ N, e.hom ≫ b = a := by
  exact ⟨fun h ↦ ⟨imageIdealEqualityIso a b h, imageIdealEqualityIso_comp a b h⟩,
    fun ⟨e, he⟩ ↦ quasicoherentImageIdeal_eq_of_iso a b e he⟩

/-- The compatible isomorphism for a fixed equality is unique. -/
theorem imageIdealEqualityIso_unique [Mono a] [Mono b]
    (h : quasicoherentImageIdeal a = quasicoherentImageIdeal b)
    (e : M ≅ N) (he : e.hom ≫ b = a) : e = imageIdealEqualityIso a b h := by
  apply Iso.ext
  apply (cancel_mono b).mp
  rw [he, imageIdealEqualityIso_comp]

/-- Starting with an actual ideal inclusion recovers that ideal, including nilpotents. -/
theorem quasicoherentImageIdeal_idealModuleι (I : X.IdealSheafData)
    [(idealModule I).IsQuasicoherent] : quasicoherentImageIdeal (idealModuleι I) = I := by
  apply Scheme.IdealSheafData.ext
  funext U
  apply SetLike.coe_injective
  exact idealModuleι_range I U

end FLT.Mazur.FCurve
