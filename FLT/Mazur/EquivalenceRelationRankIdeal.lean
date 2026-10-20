/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationRankSaturation
public import FLT.Mazur.RelativeRankStratumThickenings
public import FLT.Mazur.SmoothRadicalIdealSheaf
public import FLT.Mazur.InvariantIdealEquivalence

/-!
# Invariant equations of the full original rank strata

Inside each original rank-image open, both complete endpoints pull back the
same rank ideal. This is equality of ideals and of every ideal power, extending
rank invariance from points to all infinitesimal thickening orders.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] (e : CategoryTheory.EquivalenceRelation p q)
local instance rankIdealOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankIdealOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankIdealOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ)
local notation "U" => rankImageOpen (Over.mk p) n

/-- The entire original first endpoint over its rank-image open. -/
def rankOpenFirst : (p ⁻¹ᵁ U).toScheme ⟶ (U).toScheme := p.resLE U _ le_rfl

/-- The independent second endpoint on the same whole open relation. -/
def rankOpenSecond : (p ⁻¹ᵁ U).toScheme ⟶ (U).toScheme :=
  q.resLE U _ (rankImage_preimage_eq e n).le

instance rankOpenFirst_etale : Etale (rankOpenFirst (p := p) n) := by
  unfold rankOpenFirst
  infer_instance

instance rankOpenSecond_etale : Etale (rankOpenSecond e n) := by
  unfold rankOpenSecond
  infer_instance

omit [Etale q] in
/-- Both endpoints retain the exact original closed rank bound. -/
theorem rankIdeal_support_invariant :
    rankOpenFirst (p := p) n ⁻¹'
        ((rankStratumIdeal (Over.mk p) n).support : Set (U).toScheme) =
      rankOpenSecond e n ⁻¹'
        ((rankStratumIdeal (Over.mk p) n).support : Set (U).toScheme) := by
  ext x
  change (U).ι (rankOpenFirst (p := p) n x) ∈ rankAtMost (Over.mk p) n ↔
    (U).ι (rankOpenSecond e n x) ∈ rankAtMost (Over.mk p) n
  have hp := congrArg (fun g ↦ g x) (Scheme.Hom.resLE_comp_ι p (le_refl (p ⁻¹ᵁ U)))
  have hq := congrArg (fun g ↦ g x)
    (Scheme.Hom.resLE_comp_ι q (rankImage_preimage_eq e n).le)
  change (U).ι (rankOpenFirst (p := p) n x) = p ((p ⁻¹ᵁ U).ι x) at hp
  change (U).ι (rankOpenSecond e n x) = q ((p ⁻¹ᵁ U).ι x) at hq
  rw [hp, hq]
  exact rankAtMost_endpoint_iff e n _

variable [IsLocallyNoetherian A]

/-- Exact ideal invariance on the full relation over the rank-image open. -/
theorem rankIdeal_invariant :
    (rankStratumIdeal (Over.mk p) n).comap (rankOpenFirst (p := p) n) =
      (rankStratumIdeal (Over.mk p) n).comap (rankOpenSecond e n) := by
  let _ : IsLocallyNoetherian (U).toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (U).ι
  apply SmoothRadicalIdealSheaf.comap_eq_of_support _ _ _ _ (rankIdeal_support_invariant e n)
  rw [← Scheme.IdealSheafData.vanishingIdeal_support]
  rfl

/-- Every actual power of the rank ideal is invariant, with all nilpotents retained. -/
theorem rankIdeal_pow_invariant (k : ℕ) :
    (rankStratumIdeal (Over.mk p) n ^ k).comap (rankOpenFirst (p := p) n) =
      (rankStratumIdeal (Over.mk p) n ^ k).comap (rankOpenSecond e n) :=
  InvariantIdealRelation.pow_invariant _ (rankIdeal_invariant e n) k

end FLT.Mazur.EquivalenceRelationOrderedFrames
