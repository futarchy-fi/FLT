/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAffineTargetRigidity
public import FLT.Mazur.ArtinianProperAffineBaseChange
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Upgrading fiberwise constancy to equality over the original base

Pointwise constancy along a proper flat connected reduced family forces actual
scheme-theoretic constancy. Affine neighborhoods of the image section reduce
the statement to the original global-functions comparison. The base may carry
nilpotents; no equality-detection by geometric points of the total space is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S Y : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include hs

/-- Pointwise fiber constancy forces equality of the full original scheme maps. -/
theorem proper_eq_section_of_pointwise (a : X ⟶ Y)
    (ha : ∀ x : X, a x = a (s (f x))) : a = f ≫ s ≫ a := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (a x)) isOpen_univ
  change Y.Opens at W
  have hxV : f x ∈ s ⁻¹ᵁ (a ⁻¹ᵁ W) := by
    change a (s (f x)) ∈ W
    rwa [← ha x]
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hxV (s ⁻¹ᵁ (a ⁻¹ᵁ W)).isOpen
  change S.Opens at U
  let _ : IsAffine U.toScheme := hU
  let _ : IsAffine W.toScheme := hW
  let _ : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let q := f ∣_ U
  let j := (f ⁻¹ᵁ U).ι
  let H := (isPullback_morphismRestrict f U).flip
  let t := ArtinianProperAffineBaseChange.sectionOfSquare H s hs
  have ht : t ≫ q = 𝟙 _ :=
    ArtinianProperAffineBaseChange.sectionOfSquare_projection H s hs
  have htj : t ≫ j = U.ι ≫ s := H.lift_fst _ _ _
  let b := IsOpenImmersion.lift W.ι (j ≫ a) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change a z.val ∈ W
    rw [ha z.val]
    exact hUV z.property)
  have hb : b ≫ W.ι = j ≫ a := IsOpenImmersion.lift_fac _ _ _
  have he := congrArg (fun k ↦ k ≫ W.ι) (proper_to_affine_eq_section q t ht b)
  rw [Category.assoc, Category.assoc, hb, ← Category.assoc t j, htj,
    Category.assoc U.ι s a, ← Category.assoc q U.ι, morphismRestrict_ι] at he
  exact ⟨f ⁻¹ᵁ U, hxU, by simpa only [j, Category.assoc] using he⟩

end FLT.Mazur.FCurve
