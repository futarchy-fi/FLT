/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalCoordinateDirected

/-!
# Several principal opens with one ambient source stage

A source chart can occur in many overlaps with different denominators. All
these occurrences use one relation set in the ambient chart. Target charts
have independent relation sets, and every transition square commutes.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]

/-- Outgoing coordinate maps whose distinct principal opens share their ambient relations. -/
structure PrincipalFanStage (a : ι → A) (b : ∀ i, B i)
    (f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away (b i)) where
  /-- Relations of the one common ambient chart. -/
  source : Finset (relationIdeal R A)
  /-- Relations at each separate target. -/
  target : ∀ i, Finset (relationIdeal R (B i))
  /-- Each leg starts in its own principal open of the same ambient stage. -/
  hom : ∀ i, PrincipalStage R A (a i) source →ₐ[R] PrincipalStage R (B i) (b i) (target i)
  /-- The original maps are recovered at every leg. -/
  fac : ∀ i, (principalStageMap R (B i) (b i) (target i)).comp (hom i) =
    (f i).comp (principalStageMap R A (a i) source)

variable {a : ι → A} {b : ∀ i, B i}
  {f : ∀ i, Localization.Away (a i) →ₐ[R] Localization.Away (b i)}

/-- Extract a coordinate stage without changing its shared ambient relation set. -/
def principalFanLeg (x : PrincipalFanStage a b f) (i : ι) :
    PrincipalMapStage (a i) (b i) (f i) :=
  ⟨x.source, x.target i, x.hom i, x.fac i⟩

/-- A fan refinement increases the ambient relations and commutes on every principal open. -/
instance principalFanStagePreorder : Preorder (PrincipalFanStage a b f) where
  le x y := x.source ≤ y.source ∧ ∀ i, principalFanLeg x i ≤ principalFanLeg y i
  le_refl x := ⟨le_rfl, fun _ ↦ le_rfl⟩
  le_trans x y z hxy hyz := ⟨hxy.1.trans hyz.1, fun i ↦ (hxy.2 i).trans (hyz.2 i)⟩

/-- All target relation sets increase under a fan refinement. -/
theorem principalFan_target_mono {x y : PrincipalFanStage a b f} (h : x ≤ y) :
    x.target ≤ y.target := fun i ↦ (h.2 i).choose_spec.choose

/-- Every coordinate square commutes on the full localized source stage. -/
theorem principalFan_hom_comm {x y : PrincipalFanStage a b f} (h : x ≤ y) (i : ι) :
    (y.hom i).comp (principalTransition (a i) h.1) =
      (principalTransition (b i) (principalFan_target_mono h i)).comp (x.hom i) :=
  (h.2 i).choose_spec.choose_spec

/-- Every fixed ambient stage admits simultaneous lifts with arbitrary target bounds. -/
theorem exists_principalFanStage (s : Finset (relationIdeal R A))
    (t : ∀ i, Finset (relationIdeal R (B i))) :
    ∃ x : PrincipalFanStage a b f, x.source = s ∧ t ≤ x.target := by
  choose q ht g hg using fun i ↦ exists_principalStageMap_lift (b i) (a i) (f i) s (t i)
  exact ⟨⟨s, q, g, hg⟩, rfl, ht⟩

/-- The fan index has a stage, including when there are no outgoing maps. -/
instance principalFanStageNonempty : Nonempty (PrincipalFanStage a b f) := by
  obtain ⟨x, _, _⟩ := exists_principalFanStage (a := a) (b := b) (f := f) ∅ (fun _ ↦ ∅)
  exact ⟨x⟩

end FLT.Mazur.FiniteTypeRelationModel
