/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularCompatibleTransport
public import FLT.Mazur.CompatibleSubgroupIsoFaithful

/-!
# Coherence of constructed singular orbit comparisons

The constructed subgroup comparison is the unique one over its specified
full curve map. In particular its identity and composition laws hold for
the complete subgroup schemes, including coincident cyclic labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve
open FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F G : GeneralizedEllipticCurve S} {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ F.group))
  (e : E ≅ F) (he : ∀ i, φ i ≫ e.hom.group = ψ i)
  (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n)
  (hH : H.ideal = E.cyclicMarkingIdeal φ) (hJ : J.ideal = F.cyclicMarkingIdeal ψ)

/-- Any comparison over the prescribed full curve equals the constructed orbit comparison. -/
theorem singularOrbitCompatibleIso_unique (d : CompatibleIso H J) (hd : d.curve = e) :
    d = singularOrbitCompatibleIso φ ψ e he H J hH hJ := by
  apply CompatibleIso.ext_curve
  rw [singularOrbitCompatibleIso_curve, hd]

/-- The comparison constructed from identity labels is the actual identity. -/
theorem singularOrbitCompatibleIso_refl :
    singularOrbitCompatibleIso φ φ (Iso.refl E) (fun _ ↦ Category.comp_id _)
      H H hH hH = CompatibleIso.refl H := by
  apply CompatibleIso.ext_curve
  exact singularOrbitCompatibleIso_curve _ _ _ _ _ _ _ _

variable (χ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ G.group))
  (f : F ≅ G) (hf : ∀ i, ψ i ≫ f.hom.group = χ i)
  (A : G.FiniteSubgroup n) (hA : A.ideal = G.cyclicMarkingIdeal χ)

include he hf in
/-- Label compatibility composes on the full group without any faithfulness condition. -/
theorem singularOrbitLabel_comp (i : Multiplicative (ZMod n)) :
    φ i ≫ (e ≪≫ f).hom.group = χ i := by
  change φ i ≫ (e.hom.group ≫ f.hom.group) = _
  rw [← Category.assoc, he, hf]

/-- Constructing a comparison from a composite equals composing the constructed comparisons. -/
theorem singularOrbitCompatibleIso_trans :
    singularOrbitCompatibleIso φ χ (e ≪≫ f) (singularOrbitLabel_comp φ ψ e he χ f hf)
      H A hH hA =
    (singularOrbitCompatibleIso φ ψ e he H J hH hJ).trans
      (singularOrbitCompatibleIso ψ χ f hf J A hJ hA) := by
  apply CompatibleIso.ext_curve
  change _ = (singularOrbitCompatibleIso φ ψ e he H J hH hJ).curve ≪≫
    (singularOrbitCompatibleIso ψ χ f hf J A hJ hA).curve
  rw [singularOrbitCompatibleIso_curve, singularOrbitCompatibleIso_curve,
    singularOrbitCompatibleIso_curve]

end FLT.Mazur.GeneralizedEllipticCurve
