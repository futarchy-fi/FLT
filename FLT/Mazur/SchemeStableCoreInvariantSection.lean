/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeStableOpenCore
public import FLT.Mazur.SchemeOpenPairSectionRestriction

/-!
# Invariant sections constructed on stable cores

A section on an arbitrary open need only agree with its translates where
both are defined. Restriction then constructs an invariant section on the
finite-orbit core, retaining exact boundary and pair-relation equations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteOrbitOpenCore
open SchemeFiniteGroupQuotient FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] {X : Scheme} (ρ : G →* Aut X)
  (O : X.Opens)
  (hf : (Set.range (fun g : G ↦ (ρ g).hom ⁻¹' (O : Set X))).Finite)
local notation "C" => invariantOpen ρ O hf
local notation "hC" => invariantOpen_stable ρ O hf
local notation "j" => X.homOfLE (invariantOpen_le ρ O hf)
variable (v : Γ(O.toScheme, ⊤))
  (hv : ∀ g : G, (pairOpenFirst O (𝟙 X) (ρ g).hom).appTop v =
    (pairOpenSecond O (𝟙 X) (ρ g).hom).appTop v)

/-- Overlap equations construct a genuine invariant section on the core. -/
def invariantCoreSection : invariantCoordinates (restrictedAction ρ C hC) := by
  refine ⟨(j).appTop v, ?_⟩
  intro g
  change ((restrictedAction ρ C hC g⁻¹).hom ≫ j).appTop v = (j).appTop v
  symm
  apply pairOpen_equation_pullback O (𝟙 X) (ρ g⁻¹).hom v (hv g⁻¹) (C).ι
    j ((restrictedAction ρ C hC g⁻¹).hom ≫ j)
  · simp only [Scheme.homOfLE_ι, Category.comp_id]
  · rw [Category.assoc, Scheme.homOfLE_ι, restrictedAction_hom_ι]

/-- The construction is literal restriction of the original open section. -/
theorem invariantCoreSection_val :
    (invariantCoreSection ρ O hf v hv).val = (j).appTop v := rfl

/-- The constructed invariant section retains the exact unreduced boundary value. -/
theorem invariantCoreSection_boundary {Y : Scheme} (i : Y ⟶ X) (t : Γ(Y, ⊤))
    (hb : (i ∣_ O).appTop v = (i ⁻¹ᵁ O).ι.appTop t) :
    (i ∣_ C).appTop (invariantCoreSection ρ O hf v hv).val =
      (i ⁻¹ᵁ C).ι.appTop t :=
  open_boundary_equation_refine O C (invariantOpen_le ρ O hf) i v t hb

/-- Every full pair equation on the original open restricts to the core. -/
theorem invariantCoreSection_pair {Z : Scheme} (f g : Z ⟶ X)
    (he : (pairOpenFirst O f g).appTop v = (pairOpenSecond O f g).appTop v) :
    (pairOpenFirst C f g).appTop (invariantCoreSection ρ O hf v hv).val =
      (pairOpenSecond C f g).appTop (invariantCoreSection ρ O hf v hv).val :=
  pairOpen_equation_refine O f g C (invariantOpen_le ρ O hf) v he

end FLT.Mazur.SchemeFiniteOrbitOpenCore
