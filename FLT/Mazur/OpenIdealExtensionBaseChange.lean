/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionIdealCorrespondence

/-!
# Arbitrary base change of full ideal extension through an open

When the original open family is closed in its containing ambient, extension
of its full ideal commutes with every cartesian base change. The proof uses
actual support containment only to recover the extended ideal from its open
restriction; it does not replace the ideal by a radical or a point set.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.OpenIdealCover

variable {A B A' B' : Scheme.{u}} (i : A ⟶ B) (i' : A' ⟶ B')
variable [IsOpenImmersion i] [IsOpenImmersion i']
variable (f : A' ⟶ A) (g : B' ⟶ B) (q : IsPullback f i' i g)
variable (J : A.IdealSheafData) [IsClosedImmersion (J.subschemeι ≫ i)]

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
include q in
/-- The pulled-back extension is supported in the actual pulled-back open. -/
theorem openIdealExtension_baseChange_support :
    Set.range ((J.map i).comap g).subschemeι ⊆ Set.range i' := by
  intro y hy
  have hgy : g y ∈ Set.range (J.map i).subschemeι := by
    rw [range_subschemeι, support_comap] at hy
    rw [range_subschemeι]
    exact hy
  obtain ⟨x, hx⟩ := open_map_range i J hgy
  obtain ⟨w, _, hw⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
  exact ⟨q.isoPullback.inv w,
    (congrArg (fun h ↦ h w) q.isoPullback_inv_snd).trans hw⟩

include q in
/-- Extension of the entire ideal commutes with arbitrary cartesian base change. -/
theorem openIdealExtension_baseChange : (J.map i).comap g = (J.comap f).map i' := by
  have h : ((J.map i).comap g).comap i' = J.comap f := by
    rw [← comap_comp, ← q.w, comap_comp, open_comap_map]
  rw [← h, open_map_comap i' ((J.map i).comap g)
    (openIdealExtension_baseChange_support i i' f g q J)]

end FLT.Mazur.OpenIdealCover
