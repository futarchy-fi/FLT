/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantSections

/-!
# Invariant-sheaf section rings on identified source domains

The equalizer sheaf's sections are the original compatible-function subring.
The comparison also allows an explicitly identified source open, retaining
the transport map so that open-immersion coordinates remain usable.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- The original invariant-function subring on an invariant source open. -/
def originalInvariantSections (V : (U).Opens) (hv : src ⁻¹ᵁ V = tgt ⁻¹ᵁ V) :
    Subring Γ(U, V) :=
  RingHom.eqLocus ((src).app V).hom ((tgt).appLE V (src ⁻¹ᵁ V) hv.le).hom

/-- Every invariant sheaf section is an original invariant regular function. -/
theorem invariantSection_mem (W : TopologicalSpace.Opens (Orbit n))
    (s : (invariantSheaf n).obj.obj (op W)) :
    (invariantInclusion n).hom.app (op W) s ∈
      originalInvariantSections n (pullOpen n W).val
        (pullOpen_preimage_eq n W) := by
  have h := invariantSection_condition n W s
  rw [firstRestriction_app, secondRestriction_app] at h
  exact h

/-- Sections of the actual invariant sheaf are the original invariant-function ring. -/
def invariantSectionRingEquiv (W : TopologicalSpace.Opens (Orbit n)) :
    (invariantSheaf n).obj.obj (op W) ≃+*
      originalInvariantSections n (pullOpen n W).val
        (pullOpen_preimage_eq n W) := by
  let φ := ((invariantInclusion n).hom.app (op W)).hom.codRestrict _
    (invariantSection_mem n W)
  apply RingEquiv.ofBijective φ
  constructor
  · intro s t h
    exact invariantSection_ext n W (congrArg Subtype.val h)
  · intro s
    have hs : (firstRestriction n).hom.app (op W) s.val =
        (secondRestriction n).hom.app (op W) s.val := by
      rw [firstRestriction_app, secondRestriction_app]
      exact s.property
    obtain ⟨t, ht, _⟩ := invariantSection_existsUnique n W s.val hs
    exact ⟨t, Subtype.ext ht⟩

/-- The same section-ring comparison on any explicitly identified source domain. -/
def invariantSectionRingEquivOn (W : TopologicalSpace.Opens (Orbit n))
    (V : (U).Opens) (h : (pullOpen n W).val = V)
    (hv : src ⁻¹ᵁ V = tgt ⁻¹ᵁ V) :
    (invariantSheaf n).obj.obj (op W) ≃+* originalInvariantSections n V hv := by
  subst V
  exact invariantSectionRingEquiv n W

/-- The domain-identified comparison retains the original source pullback, with its transport. -/
theorem invariantSectionRingEquivOn_val (W : TopologicalSpace.Opens (Orbit n))
    (V : (U).Opens) (h : (pullOpen n W).val = V)
    (hv : src ⁻¹ᵁ V = tgt ⁻¹ᵁ V)
    (s : (invariantSheaf n).obj.obj (op W)) :
    (invariantSectionRingEquivOn n W V h hv s).val =
      (U).presheaf.map (eqToHom (congrArg op h))
        ((invariantInclusion n).hom.app (op W) s) := by
  subst V
  simp only [eqToHom_refl]
  rw [(U).presheaf.map_id]
  rfl

end FLT.Mazur.CyclicCharacteristicOrbit
