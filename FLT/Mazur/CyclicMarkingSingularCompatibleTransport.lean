/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularTransport

/-!
# Compatible transport of full singular orbit subgroups

Transported full orbit ideals identify the actual subgroup schemes over a
given full curve isomorphism. The comparison keeps the prescribed curve map
and hence each original auxiliary section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ F.group))
  (e : E ≅ F) (he : ∀ i, φ i ≫ e.hom.group = ψ i)
  (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n)
  (hH : H.ideal = E.cyclicMarkingIdeal φ) (hJ : J.ideal = F.cyclicMarkingIdeal ψ)

/-- Exact orbit ideals give a comparison of full subgroup schemes over the prescribed curve. -/
def singularOrbitCompatibleIso : FiniteSubgroup.CompatibleIso H J :=
  (H.transportCompatibleIso e).trans
    (FiniteSubgroup.compatibleIsoOfIdealEq (H.transport e) J
      ((singularOrbitSubgroup_transport_ideal φ ψ e he H hH).trans hJ.symm))

/-- The subgroup comparison retains the specified full curve isomorphism. -/
theorem singularOrbitCompatibleIso_curve :
    (singularOrbitCompatibleIso φ ψ e he H J hH hJ).curve = e := by
  change e.trans (Iso.refl F) = e
  exact Iso.trans_refl e

/-- All prescribed auxiliary sections retain their original compatibility equation. -/
theorem singularOrbitCompatibleIso_section (p : 𝟙_ (Over S) ⟶ E.group)
    (q : 𝟙_ (Over S) ⟶ F.group) (hp : p ≫ e.hom.group = q) :
    p ≫ (singularOrbitCompatibleIso φ ψ e he H J hH hJ).curve.hom.group = q := by
  rw [singularOrbitCompatibleIso_curve]
  exact hp

/-- The original cyclic sections retain exactly the same group comparison. -/
theorem singularOrbitCompatibleIso_label (i : Multiplicative (ZMod n)) :
    φ i ≫ (singularOrbitCompatibleIso φ ψ e he H J hH hJ).curve.hom.group = ψ i :=
  singularOrbitCompatibleIso_section φ ψ e he H J hH hJ _ _ (he i)

end FLT.Mazur.GeneralizedEllipticCurve
