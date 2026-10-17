/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAdicVanishingOpen
public import FLT.Mazur.UniformAdicDiscrepancySeparation

/-!
# A uniform open for arbitrarily many adically vanishing sections

One basic open in each affine chart kills every section that vanishes at all
adic orders. Consequently the largest open on which an arbitrary family is
zero contains the full adic support. No finite generation of the family over
a smaller scalar ring is required or claimed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeAdicVanishingNeighborhood
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme}

/-- One affine basic open kills all elements of the adic intersection at once. -/
theorem exists_affine_uniform_neighborhood [IsLocallyNoetherian X]
    (J : X.IdealSheafData) (V : X.affineOpens) :
    ∃ s : Γ(X, V), 1 - s ∈ J.ideal V ∧
      (J.support : Set X) ∩ V.1 ⊆ X.basicOpen s ∧
      ∀ a : Γ(X, V), (∀ n : ℕ, a ∈ J.ideal V ^ (n + 1)) →
        X.presheaf.map (homOfLE (X.basicOpen_le s)).op a = 0 := by
  let _ := IsLocallyNoetherian.component_noetherian V
  obtain ⟨s, hs, ha⟩ := AdicDiscrepancySeparation.exists_uniform_ring_annihilator (J.ideal V)
  exact ⟨s, hs, support_subset_basicOpen J V s hs,
    fun a h ↦ restrict_eq_zero_of_annihilator V.1 s a (ha a h)⟩

variable {ι : Type*} (a : ι → Γ(X, ⊤))

/-- The largest open on which all the specified sections vanish simultaneously. -/
def uniformVanishingOpen : X.Opens := ⨅ i, vanishingOpen (a i)

/-- Every section of the family vanishes on the same actual open subscheme. -/
theorem uniformVanishingOpen_inclusion_zero (i : ι) :
    (uniformVanishingOpen a).ι.appTop (a i) = 0 := by
  have h : uniformVanishingOpen a ≤ vanishingOpen (a i) := iInf_le _ i
  have hz := congrArg (fun z ↦ (X.homOfLE h).appTop z)
    (vanishingOpen_inclusion_zero (a i))
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    Scheme.homOfLE_ι, map_zero] using hz

/-- All-order vanishing puts the whole closed support inside a common actual open. -/
theorem support_subset_uniformVanishingOpen [IsLocallyNoetherian X]
    (J : X.IdealSheafData)
    (ha : ∀ (i : ι) (V : X.affineOpens) (n : ℕ),
      X.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op (a i) ∈ J.ideal V ^ (n + 1)) :
    (J.support : Set X) ⊆ uniformVanishingOpen a := by
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨s, _, hs, hz⟩ := exists_affine_uniform_neighborhood J ⟨V, hV⟩
  have hle : X.basicOpen s ≤ uniformVanishingOpen a := by
    apply le_iInf
    intro i
    apply le_vanishingOpen
    have h := hz (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (a i)) (ha i ⟨V, hV⟩)
    simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← op_comp, homOfLE_comp] using h
  exact hle (hs ⟨hx, hxV⟩)

/-- Every further scheme test through the common open kills every section. -/
theorem uniformVanishingOpen_test {T : Scheme}
    (g : T ⟶ (uniformVanishingOpen a).toScheme) (i : ι) :
    (g ≫ (uniformVanishingOpen a).ι).appTop (a i) = 0 := by
  rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply,
    uniformVanishingOpen_inclusion_zero, map_zero]

end FLT.Mazur.SchemeAdicVanishingNeighborhood
