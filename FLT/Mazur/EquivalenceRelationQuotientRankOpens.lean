/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryFaithful
public import FLT.Mazur.EquivalenceRelationRankSaturation

/-!
# Original rank opens on the affine normalized quotient

All rank opens descend through the actual normalized-frame quotient, not only
its matching-rank closed locus. Their inverse images are the original opens.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local instance quotientRankOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance quotientRankOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance quotientRankOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

omit [IsAffine U.toScheme] in
/-- Every original rank open is stable under the restricted normalized action. -/
theorem chart_rankImage_stable (m : ℕ) (g : Equiv.Perm (Fin n)) (x : U.toScheme)
    (hx : first p q (Fin n) o (U.ι x) ∈ rankImageOpen (Over.mk p) m) :
    first p q (Fin n) o (U.ι ((ρ g).hom x)) ∈ rankImageOpen (Over.mk p) m := by
  have h := EquivalenceRelationOrderedFrames.rankImage_endpoint_iff e m
    (actionArrow (p := p) (q := q) (Fin n) o g (U.ι x))
  have hp := congrArg (fun f ↦ f (U.ι x)) (actionArrow_first (p := p) (q := q) (Fin n) o g)
  have hq := congrArg (fun f ↦ f (U.ι x)) (actionArrow_second e (Fin n) o g)
  have hu := congrArg (fun f ↦ f x)
    (restrictedAction_hom_ι (action e (Fin n) o) U hU g)
  change p _ = _ at hp
  change q _ = _ at hq
  change U.ι ((ρ g).hom x) = (action e (Fin n) o g).hom (U.ι x) at hu
  rw [hu]
  exact hq ▸ (h.mp (hp.symm ▸ hx))

/-- The actual quotient open of original frames of rank at least the specified size. -/
def quotientRankOpen (m : ℕ) : (Spec (.of (invariantCoordinates ρ))).Opens :=
  ⟨quotientMap ρ '' ((U.ι ≫ first p q (Fin n) o) ⁻¹ᵁ rankImageOpen (Over.mk p) m),
    quotientMap_image_isOpen ρ _
      ((U.ι ≫ first p q (Fin n) o) ⁻¹ᵁ rankImageOpen (Over.mk p) m).isOpen
      (chart_rankImage_stable n o U e hU m)⟩

/-- Descent retains exactly the original rank open, including at residual points. -/
theorem quotientRankOpen_preimage (m : ℕ) :
    quotientMap ρ ⁻¹ᵁ quotientRankOpen n o U e hU m =
      (U.ι ≫ first p q (Fin n) o) ⁻¹ᵁ rankImageOpen (Over.mk p) m := by
  apply TopologicalSpace.Opens.ext
  exact quotientMap_saturated ρ _ (chart_rankImage_stable n o U e hU m)

/-- Rank opens in the unchanged invariant spectrum form a decreasing filtration. -/
theorem quotientRankOpen_antitone : Antitone (quotientRankOpen n o U e hU) := by
  intro a b hab
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, rankImageOpen_antitone (Over.mk p) hab hx, rfl⟩

/-- The retained original frame guarantees the bottom of the quotient filtration. -/
theorem quotientRankOpen_frame : quotientRankOpen n o U e hU n = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨x, rfl⟩ := (quotientMap ρ).surjective z
  exact ⟨x, ⟨inclusion p q (Fin n) o (U.ι x), rfl⟩, rfl⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
