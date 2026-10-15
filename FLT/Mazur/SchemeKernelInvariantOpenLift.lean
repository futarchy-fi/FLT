/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismOpenImage

/-!
# Original kernel inverses from invariant source opens

An open source invariant under the candidate kernel retains both independent
endpoints whenever it retains the first. A full kernel reconstruction on that
source therefore constructs an inverse on an actual open of the ORIGINAL
candidate kernel. No reduction of the test scheme or coefficient target occurs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeKernelInvariantOpenLift
set_option backward.isDefEq.respectTransparency false
variable {D A T : Scheme.{u}} (p q : D ⟶ A) (v : A ⟶ T)
  (h : p ≫ v = q ≫ v) (W : A.Opens)
local notation "x" => pullback.fst v v
local notation "y" => pullback.snd v v
/-- The actual original kernel open selected by its first source endpoint. -/
def openDomain : (pullback v v : Scheme).Opens := pullback.fst v v ⁻¹ᵁ W
local notation "U" => openDomain v W

/-- A reconstructed restricted relation supplies a literal original arrow on a kernel open. -/
theorem exists_lift
    (hW : x ⁻¹ᵁ W = y ⁻¹ᵁ W) {E : Scheme.{u}}
    (r t : E ⟶ W.toScheme) (j : E ⟶ D)
    (hr : j ≫ p = r ≫ W.ι) (ht : j ≫ q = t ≫ W.ι)
    (H : IsPullback r t (W.ι ≫ v) (W.ι ≫ v)) :
    ∃ a : (U).toScheme ⟶ D, a ≫ pullback.lift p q h = (U).ι := by
  let a := (x).resLE W U le_rfl
  let b := (y).resLE W U hW.le
  have ha : a ≫ W.ι = (U).ι ≫ x := (x).resLE_comp_ι le_rfl
  have hb : b ≫ W.ι = (U).ι ≫ y := (y).resLE_comp_ι hW.le
  have hab : a ≫ (W.ι ≫ v) = b ≫ (W.ι ≫ v) := by
    rw [← Category.assoc, ← Category.assoc, ha, hb, Category.assoc,
      Category.assoc, pullback.condition]
  refine ⟨H.lift a b hab ≫ j, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, hr,
      ← Category.assoc, H.lift_fst, ha]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, ht,
      ← Category.assoc, H.lift_snd, hb]

/-- The inverse exists on the whole original kernel open, not merely the seed's image points. -/
theorem le_inverseLocus
    (hW : x ⁻¹ᵁ W = y ⁻¹ᵁ W) {E : Scheme.{u}}
    (r t : E ⟶ W.toScheme) (j : E ⟶ D)
    (hr : j ≫ p = r ≫ W.ι) (ht : j ≫ q = t ≫ W.ι)
    (H : IsPullback r t (W.ι ≫ v) (W.ι ≫ v)) :
    U ≤ MonomorphismOpenImage.locus (pullback.lift p q h) := by
  obtain ⟨a, ha⟩ := exists_lift p q v h W hW r t j hr ht H
  exact MonomorphismOpenImage.le_locus _ U a ha

end FLT.Mazur.SchemeKernelInvariantOpenLift
