/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationPrincipalRestriction
public import FLT.Mazur.RingedSpaceIdealLocus

/-!
# Coverage after a full relation comparison

Whether an invariant ideal locus covers the inverse image of its domain can
be tested on an affine source of the target relation. Only the images of the
original ideal elements are used. In particular this tests boundary coverage
without asking that the locus cover the whole ambient quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme.{u}} {A U : Over S} {A' U' : Over S'}
  {p q : A ⟶ U} {p' q' : A' ⟶ U'}
  (e : CategoryTheory.EquivalenceRelation p q)
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (g : U'.left ⟶ U.left) (r : A'.left ⟶ A.left)
  (hp : r ≫ p.left = p'.left ≫ g) (hq : r ≫ q.left = q'.left ≫ g)
  (W : Opens (Orbit e)) (I : Ideal ((invariantSheaf e).obj.obj (op W)))
local notation "m" => invariantMap e e' g r hp hq
local notation "W'" =>
  (Functor.obj (Opens.map (PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.toHom m))) W)
local notation "N'" =>
  (Functor.obj (Opens.map (PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.toHom m)))
    (sectionIdealOpen (ringedSpace e) W I))

/-- The original ideal's images in the actual compared source section ring. -/
def pulledIdealSourceGenerators : Set Γ(U'.left, (pullOpen e' W').val) :=
  (fun a : (invariantSheaf e).obj.obj (op W) ↦
    (invariantInclusion e').hom.app (op W') ((m).c.app (op W) a)) '' (I : Set _)

/-- The pulled source domain is exactly the union of these actual source basic opens. -/
theorem pullOpen_preimage_sectionIdealOpen :
    (pullOpen e' N').val =
      ⨆ a : pulledIdealSourceGenerators e e' g r hp hq W I, U'.left.basicOpen a.val := by
  ext x
  change (m).base (projection e' x) ∈ sectionIdealOpen (ringedSpace e) W I ↔ _
  rw [mem_sectionIdealOpen]
  have hx (a : (invariantSheaf e).obj.obj (op W)) :
      (m).base (projection e' x) ∈ RingedSpace.basicOpen (ringedSpace e) a ↔
        x ∈ U'.left.basicOpen
          ((invariantInclusion e').hom.app (op W') ((m).c.app (op W) a)) := by
    change x ∈ (pullOpen e' ((Opens.map (m).base).obj
      (invariantPrincipal e W a))).val ↔ _
    rw [invariantMap_principal, pullOpen_invariantPrincipal]
  constructor
  · rintro ⟨a, ha, hxa⟩
    exact Opens.mem_iSup.mpr ⟨⟨_, ⟨a, ha, rfl⟩⟩, (hx a).mp hxa⟩
  · intro h
    obtain ⟨⟨b, a, ha, hab⟩, hxb⟩ := Opens.mem_iSup.mp h
    subst b
    exact ⟨a, ha, (hx a).mpr hxb⟩

/-- Covering the compared quotient domain is exactly the unit-ideal test on its affine source. -/
theorem preimage_sectionIdealOpen_eq_iff_sourceIdeal_top
    (hW' : IsAffineOpen (pullOpen e' W').val) :
    N' = W' ↔ Ideal.span (pulledIdealSourceGenerators e e' g r hp hq W I) = ⊤ := by
  rw [← hW'.iSup_basicOpen_eq_self_iff, ← pullOpen_preimage_sectionIdealOpen]
  constructor
  · intro h
    rw [h]
  · intro h
    apply (opensOrderIso e').injective
    exact Subtype.ext h

/-- The pulled unit-ideal equation is a finite coefficient identity in the compared source. -/
theorem pulledIdealSource_eq_top_iff_certificate :
    Ideal.span (pulledIdealSourceGenerators e e' g r hp hq W I) = ⊤ ↔
      ∃ c : I →₀ (sourceSheaf e').obj.obj (op W'),
        c.sum (fun a b ↦ b * (invariantInclusion e').hom.app (op W')
          ((m).c.app (op W) a.val)) = 1 := by
  have h : pulledIdealSourceGenerators e e' g r hp hq W I =
      Set.range (fun a : I ↦ (invariantInclusion e').hom.app (op W')
        ((m).c.app (op W) a.val)) := by
    ext a
    simp only [pulledIdealSourceGenerators, Set.mem_image, Set.mem_range,
      Subtype.exists, exists_prop, SetLike.mem_coe]
  rw [h, Ideal.eq_top_iff_one, Finsupp.mem_ideal_span_range_iff_exists_finsupp]
  rfl

end FLT.Mazur.RelativeRelationOrbit
