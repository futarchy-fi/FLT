/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealFamilies
public import FLT.Mazur.FiniteFamilySupportBaseChange

/-!
# Exact support opens for full relative ideal families

The finite projection constructs the largest test-base open over which the
entire family lies in an original ambient open. Its factorization criterion
works after arbitrary base change, without reducedness or positive degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {A S X Y : Scheme.{u}} (a : A ⟶ S) (d : ℕ) (s : X ⟶ S)
variable (J : RelativeIdealFamilies a d s) (U : A.Opens)

/-- The actual base open where the entire finite family lies in the original ambient open. -/
def relativeIdealFamilySupportOpen : X.Opens := by
  let _ : IsFinite (J.val.subschemeι ≫ pullback.fst s a) := J.property.1
  exact finiteFamilySupportOpen (J.val.subschemeι ≫ pullback.fst s a)
    ((J.val.subschemeι ≫ pullback.snd s a) ⁻¹ᵁ U)

/-- Membership in the support open means containment of the entire actual fiber. -/
theorem mem_relativeIdealFamilySupportOpen (x : X) :
    x ∈ relativeIdealFamilySupportOpen a d s J U ↔
      ∀ y : J.val.subscheme, (J.val.subschemeι ≫ pullback.fst s a) y = x →
        (J.val.subschemeι ≫ pullback.snd s a) y ∈ U := by
  let _ : IsFinite (J.val.subschemeι ≫ pullback.fst s a) := J.property.1
  exact mem_finiteFamilySupportOpen _ _ x

/-- An arbitrary test base enters the support open exactly when its full family enters U. -/
theorem relativeIdealFamilySupportOpen_factorization (t : Y ⟶ S)
    (g : Y ⟶ X) (hg : g ≫ s = t) :
    Set.range g ⊆ relativeIdealFamilySupportOpen a d s J U ↔
      Set.range ((relativeIdealFamilyBaseChange a d s t g hg J).val.subschemeι ≫
        pullback.snd t a) ⊆ U := by
  let _ : IsFinite (J.val.subschemeι ≫ pullback.fst s a) := J.property.1
  let m := relativeIdealAmbientMap a s t g hg
  have h := range_subset_finiteFamilySupportOpen_iff
    (J.val.subschemeι ≫ pullback.fst s a) ((J.val.subschemeι ≫ pullback.snd s a) ⁻¹ᵁ U)
    (restrictionMap J.val m) ((J.val.comap m).subschemeι ≫ pullback.fst t a) g
    (restrictionMap_base_isPullback J.val m (relativeIdealAmbientMap_isPullback a s t g hg))
  change Set.range g ⊆ relativeIdealFamilySupportOpen a d s J U ↔
    Set.range (restrictionMap J.val m) ⊆
      (J.val.subschemeι ≫ pullback.snd s a) ⁻¹' (U : Set A) at h
  rw [← Set.image_subset_iff, ← Set.range_comp] at h
  change _ ↔ Set.range (restrictionMap J.val m ≫ J.val.subschemeι ≫ pullback.snd s a) ⊆ U at h
  rw [← Category.assoc, restrictionMap_immersion, Category.assoc,
    relativeIdealAmbientMap_snd] at h
  exact h

end FLT.Mazur.ClosedIdealCover
