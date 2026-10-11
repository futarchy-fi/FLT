/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantSections

/-!
# Invariant-sheaf section rings on identified source domains

The equalizer sheaf's sections are the original compatible-function subring.
The comparison also allows an explicitly identified source open, retaining
the transport map so that open-immersion coordinates remain usable.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- The original invariant-function subring on an invariant source open. -/
def originalInvariantSections (V : U.left.Opens) (hv : p.left ⁻¹ᵁ V = q.left ⁻¹ᵁ V) :
    Subring Γ(U.left, V) :=
  RingHom.eqLocus (p.left.app V).hom (q.left.appLE V (p.left ⁻¹ᵁ V) hv.le).hom

/-- Every invariant sheaf section is an original invariant regular function. -/
theorem invariantSection_mem (W : TopologicalSpace.Opens (Orbit e))
    (s : (invariantSheaf e).obj.obj (op W)) :
    (invariantInclusion e).hom.app (op W) s ∈
      originalInvariantSections (p := p) (q := q) (pullOpen e W).val
        (pullOpen_preimage_eq e W) := by
  have h := invariantSection_condition e W s
  rw [firstRestriction_app, secondRestriction_app] at h
  exact h

/-- Sections of the actual invariant sheaf are the original invariant-function ring. -/
def invariantSectionRingEquiv (W : TopologicalSpace.Opens (Orbit e)) :
    (invariantSheaf e).obj.obj (op W) ≃+*
      originalInvariantSections (p := p) (q := q) (pullOpen e W).val
        (pullOpen_preimage_eq e W) := by
  let φ := ((invariantInclusion e).hom.app (op W)).hom.codRestrict _
    (invariantSection_mem e W)
  apply RingEquiv.ofBijective φ
  constructor
  · intro s t h
    exact invariantSection_ext e W (congrArg Subtype.val h)
  · intro s
    have hs : (firstRestriction e).hom.app (op W) s.val =
        (secondRestriction e).hom.app (op W) s.val := by
      rw [firstRestriction_app, secondRestriction_app]
      exact s.property
    obtain ⟨t, ht, _⟩ := invariantSection_existsUnique e W s.val hs
    exact ⟨t, Subtype.ext ht⟩

/-- The same section-ring comparison on any explicitly identified source domain. -/
def invariantSectionRingEquivOn (W : TopologicalSpace.Opens (Orbit e))
    (V : U.left.Opens) (h : (pullOpen e W).val = V)
    (hv : p.left ⁻¹ᵁ V = q.left ⁻¹ᵁ V) :
    (invariantSheaf e).obj.obj (op W) ≃+* originalInvariantSections (p := p) (q := q) V hv := by
  subst V
  exact invariantSectionRingEquiv e W

/-- The domain-identified comparison retains the original source pullback, with its transport. -/
theorem invariantSectionRingEquivOn_val (W : TopologicalSpace.Opens (Orbit e))
    (V : U.left.Opens) (h : (pullOpen e W).val = V)
    (hv : p.left ⁻¹ᵁ V = q.left ⁻¹ᵁ V)
    (s : (invariantSheaf e).obj.obj (op W)) :
    (invariantSectionRingEquivOn e W V h hv s).val =
      U.left.presheaf.map (eqToHom (congrArg op h))
        ((invariantInclusion e).hom.app (op W) s) := by
  subst V
  simp only [eqToHom_refl]
  rw [U.left.presheaf.map_id]
  rfl

end FLT.Mazur.RelativeRelationOrbit
