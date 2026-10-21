/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameRankImage
public import FLT.Mazur.RankStratumClopenStabilization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Closed rank images for finite original projections

Finite products of the original finite scheme remain finite. The distinct
frame inclusion is clopen, so every full frame image is closed. This
constructs stabilization at all ranks without a separate closedness input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}}

/-- A finite product over the base retains finiteness of the full original sources. -/
theorem finite_product_hom {I : Type} [Finite I] (X : I → Over S)
    [∀ i, IsFinite (X i).hom] : IsFinite (∏ᶜ X).hom := by
  let _ := Fintype.ofFinite I
  let _ : MorphismProperty.HasOfPostcompProperty @IsFinite @IsFinite :=
    ⟨fun f g hg hfg ↦ by
      let _ : IsFinite g := hg
      let _ : IsFinite (f ≫ g) := hfg
      exact IsFinite.of_comp f g⟩
  let Y : I → MorphismProperty.Over @IsFinite ⊤ S := fun i ↦ ⟨X i, inferInstance⟩
  let F := MorphismProperty.Over.forget @IsFinite ⊤ S
  let e := PreservesProduct.iso F Y
  let _ : IsFinite (F.obj (∏ᶜ Y)).hom := (∏ᶜ Y).prop
  have h : IsFinite (e.inv.left ≫ (F.obj (∏ᶜ Y)).hom) := inferInstance
  rw [e.inv.w] at h
  exact h

variable (E : Over S) [Etale E.hom] [IsSeparated E.hom] [IsFinite E.hom]

/-- The entire ordered distinct frame scheme is finite over the unchanged base. -/
theorem distinctScheme_finite (I : Type) [Fintype I] :
    IsFinite (distinctScheme E I).hom := by
  let _ : IsFinite (tuples E I).hom := finite_product_hom (fun _ : I ↦ E)
  let _ : IsClosedImmersion (distinctOpen E I).ι := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    exact distinctOpen_isClosed E I
  change IsFinite ((distinctOpen E I).ι ≫ (tuples E I).hom)
  infer_instance

/-- Every original rank-image open is closed for a finite first projection. -/
theorem rankImageOpen_isClosed_of_finite (n : ℕ) : IsClosed (rankImageOpen E n : Set S) := by
  let _ := distinctScheme_finite E (Fin n)
  exact (distinctScheme E (Fin n)).hom.isClosedMap.isClosed_range

/-- Noetherian geometry constructs stationary ideal powers at every finite-relation rank. -/
theorem exists_rankStratum_stable_of_finite [IsNoetherian S] (n : ℕ) :
    ∃ K : ℕ, ∀ l, K ≤ l → rankStratumIdeal E n ^ (l + 1) =
      rankStratumIdeal E n ^ (K + 1) :=
  exists_rankStratum_stable_of_next_closed E n (rankImageOpen_isClosed_of_finite E (n + 1))

end FLT.Mazur.RelativeOrderedTuples
