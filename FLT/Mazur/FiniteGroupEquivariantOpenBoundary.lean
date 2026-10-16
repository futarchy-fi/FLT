/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupOpenRestriction
public import FLT.Mazur.SchemeFiniteGroupFreeBoundaryIdeal

/-!
# Exact equivariant boundaries on stable affine opens

An equivariant closed immersion restricts to the actual inverse image of every
stable source open. Freeness gives invariant coefficient lifts and reconstructs
the whole original boundary ideal on each affine open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] {X Y : Scheme}
  (ρ : G →* Aut X) (τ : G →* Aut Y) (i : X ⟶ Y)
  (hi : ∀ g : G, (ρ g).hom ≫ i = i ≫ (τ g).hom)
  (U : Y.Opens) (hU : ∀ g : G, (τ g).hom ⁻¹ᵁ U = U)

include hi hU in
/-- The actual inverse-image boundary open is stable, with no reduction of its scheme. -/
theorem boundaryOpen_stable (g : G) : (ρ g).hom ⁻¹ᵁ (i ⁻¹ᵁ U) = i ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, hi, Scheme.Hom.comp_preimage, hU]

/-- The original boundary action restricted to the actual inverse-image open. -/
def boundaryOpenAction : G →* Aut (i ⁻¹ᵁ U).toScheme :=
  restrictedAction ρ (i ⁻¹ᵁ U) (boundaryOpen_stable ρ τ i hi U hU)

/-- The original closed immersion remains equivariant on the source open. -/
@[reassoc] theorem boundaryOpen_equivariant (g : G) :
    (boundaryOpenAction ρ τ i hi U hU g).hom ≫ i ∣_ U =
      i ∣_ U ≫ (restrictedAction τ U hU g).hom := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι]
  change ((restrictedAction ρ (i ⁻¹ᵁ U) _ g).hom ≫ (i ⁻¹ᵁ U).ι ≫ i) = _
  rw [← Category.assoc, restrictedAction_hom_ι, Category.assoc, hi,
    ← Category.assoc, ← morphismRestrict_ι]
  rw [Category.assoc, Category.assoc, restrictedAction_hom_ι]

variable (hfree : ∀ (K : Type) [Field K] (a : Spec (.of K) ⟶ Y) (g : G),
  a ≫ (τ g).hom = a → g = 1)
include hfree

/-- The restricted moving action remains free on all field-valued tests. -/
theorem restrictedAction_free (K : Type) [Field K] (a : Spec (.of K) ⟶ U.toScheme)
    (g : G) (hg : a ≫ (restrictedAction τ U hU g).hom = a) : g = 1 := by
  apply hfree K (a ≫ U.ι) g
  have h := congrArg (fun f ↦ f ≫ U.ι) hg
  simpa only [Category.assoc, restrictedAction_hom_ι] using h

variable [Finite G] [IsClosedImmersion i]
local notation "ρU" => boundaryOpenAction ρ τ i hi U hU
local notation "τU" => restrictedAction τ U hU
local notation "hι" => boundaryOpen_equivariant ρ τ i hi U hU
open SchemeFiniteGroupQuotient

/-- Every invariant boundary function lifts on the actual stable affine source. -/
theorem boundaryOpen_invariantMap_surjective (ha : IsAffineOpen U) :
    Function.Surjective (invariantMap ρU τU (i ∣_ U) hι) := by
  let _ : IsAffine U.toScheme := ha
  exact invariantMap_surjective_of_free τU
    (restrictedAction_free τ U hU hfree) ρU (i ∣_ U) hι

/-- Every boundary section has a finite source identity on this exact affine chart. -/
theorem boundaryOpen_certificate (ha : IsAffineOpen U)
    (t : invariantCoordinates ρU) :
    ∃ a : sectionLiftIdeal (invariantMap ρU τU (i ∣_ U) hι) t →₀
        Γ((i ⁻¹ᵁ U).toScheme, ⊤),
      a.sum (fun v b ↦ b * (invariantMap ρU τU (i ∣_ U) hι v.val).val) = 1 := by
  let _ : IsAffine U.toScheme := ha
  exact invariant_boundary_certificate_of_free τU
    (restrictedAction_free τ U hU hfree) ρU (i ∣_ U) hι t

omit [IsClosedImmersion i] in
/-- Quotient boundary equations extend back to the full original ideal, including nilpotents. -/
theorem boundaryOpen_kernel_extension (ha : IsAffineOpen U) :
    (RingHom.ker (invariantMap ρU τU (i ∣_ U) hι)).map
      (let _ := SchemeCoordinateAction.coordinateAction τU
       FiniteGroupQuotient.inclusion G Γ(U.toScheme, ⊤)) =
        RingHom.ker (i ∣_ U).appTop.hom := by
  let _ : IsAffine U.toScheme := ha
  exact invariantMap_ker_extension ρU τU (i ∣_ U) hι
    (restrictedAction_free τ U hU hfree)

end FLT.Mazur.FiniteGroupRestriction
