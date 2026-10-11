/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyRingedOpenImage
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The union of actual scheme charts is a scheme

Open immersions from schemes into a locally ringed space endow their image
union with a scheme structure. The underlying locally ringed space is exactly
the restriction of the original space, including the original structure sheaf.
No coverage of the entire ambient space is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u v
namespace FLT.Mazur.LocallyRingedSchemeChartUnion
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {Z : LocallyRingedSpace.{u}} {ι : Type v} (X : ι → Scheme.{u})
  (f : ∀ i, (X i).toLocallyRingedSpace ⟶ Z)
  [hf : ∀ i, LocallyRingedSpace.IsOpenImmersion (f i)]

/-- The open union of the actual images of the scheme charts. -/
def chartUnion : Opens Z :=
  ⨆ i, ⟨Set.range (f i).base, (hf i).base_open.isOpen_range⟩

/-- Membership in the union means membership in one actual chart image. -/
theorem mem_chartUnion (z : Z) : z ∈ chartUnion X f ↔ ∃ i, z ∈ Set.range (f i).base :=
  Opens.mem_iSup

/-- Each original chart factors through the restriction to the union. -/
def chartToUnion (i : ι) : (X i).toLocallyRingedSpace ⟶
    Z.restrict (chartUnion X f).isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift
    (Z.ofRestrict (chartUnion X f).isOpenEmbedding) (f i) (by
      rw [show Set.range (Z.ofRestrict (chartUnion X f).isOpenEmbedding).base =
        (chartUnion X f).carrier from Subtype.range_val]
      intro z hz
      exact (mem_chartUnion X f z).mpr ⟨i, hz⟩)

/-- The factored map remains the original chart after inclusion in the ambient space. -/
theorem chartToUnion_comp (i : ι) : chartToUnion X f i ≫
    Z.ofRestrict (chartUnion X f).isOpenEmbedding = f i :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

instance chartToUnion_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (chartToUnion X f i) := by
  unfold chartToUnion LocallyRingedSpace.IsOpenImmersion.lift
  infer_instance

/-- The original scheme charts jointly cover the actual restricted locally ringed space. -/
theorem chartToUnion_covers (z : Z.restrict (chartUnion X f).isOpenEmbedding) :
    ∃ i, z ∈ Set.range (chartToUnion X f i).base := by
  obtain ⟨i, x, hx⟩ := (mem_chartUnion X f z.val).mp z.property
  refine ⟨i, x, ?_⟩
  apply Subtype.ext
  have he := congrArg (fun k : (X i).toLocallyRingedSpace ⟶ Z ↦ k.base x)
    (chartToUnion_comp X f i)
  exact he.trans hx

/-- The scheme structure on the union uses precisely the original restricted sheaf. -/
def scheme : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme
    (Z.restrict (chartUnion X f).isOpenEmbedding) (by
      intro z
      obtain ⟨i, x, rfl⟩ := chartToUnion_covers X f z
      obtain ⟨A, a, ha, y, hy⟩ := (X i).exists_Spec_apply_eq x
      refine ⟨A, a.toLRSHom ≫ chartToUnion X f i, ⟨y, ?_⟩, inferInstance⟩
      change (chartToUnion X f i).base (a y) = (chartToUnion X f i).base x
      rw [hy])

/-- The constructed scheme retains the original restriction verbatim. -/
theorem scheme_toLocallyRingedSpace : (scheme X f).toLocallyRingedSpace =
    Z.restrict (chartUnion X f).isOpenEmbedding := rfl

end FLT.Mazur.LocallyRingedSchemeChartUnion
