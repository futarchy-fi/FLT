/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientCartesian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Affine base charts subordinate to quotient charts

Every base change admits an affine open cover whose maps land in individual
quotient charts. Flatness of the original base morphism gives flat maps on
these actual affine charts. No separation assumption on the new base is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X S : Scheme.{u}} [X.IsSeparated]
variable (ρ : G →* Aut X) (f : S ⟶ glued ρ)

/-- An affine open of the new base lying over an actual quotient chart. -/
abbrev BaseChart :=
  {p : Chart ρ × S.affineOpens // p.2.val ≤ f ⁻¹ᵁ (chartMap ρ p.1).opensRange}

/-- Every point of the new base lies in a subordinate affine base chart. -/
theorem exists_baseChart (s : S) : ∃ c : BaseChart ρ f, s ∈ c.val.2.val := by
  obtain ⟨U, z, hz⟩ := exists_chartMap ρ (f s)
  have hs : s ∈ f ⁻¹ᵁ (chartMap ρ U).opensRange := ⟨z, hz⟩
  obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hs
  exact ⟨⟨⟨U, ⟨V, hV⟩⟩, hVU⟩, hsV⟩

/-- The constructed affine base opens cover the entire new base. -/
theorem baseCharts_cover : ⨆ c : BaseChart ρ f, c.val.2.val = ⊤ := by
  apply top_le_iff.mp
  intro s _
  obtain ⟨c, hc⟩ := exists_baseChart ρ f s
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨c, hc⟩

/-- The actual open cover of the new base, subordinate to quotient charts. -/
def baseCover : S.OpenCover :=
  S.openCoverOfIsOpenCover (fun c : BaseChart ρ f ↦ c.val.2.val) (baseCharts_cover ρ f)

/-- Containment of the actual scheme image in the chosen quotient chart. -/
lemma baseChart_range (c : BaseChart ρ f) :
    Set.range (c.val.2.val.ι ≫ f) ⊆ Set.range (chartMap ρ c.val.1) := by
  rintro _ ⟨s, rfl⟩
  exact c.property s.property

/-- The actual map from an affine base chart to its chosen affine quotient chart. -/
def baseChartMap (c : BaseChart ρ f) :
    c.val.2.val.toScheme ⟶ quotient (action ρ c.val.1) :=
  IsOpenImmersion.lift (chartMap ρ c.val.1) (c.val.2.val.ι ≫ f) (baseChart_range ρ f c)

/-- The chart lift retains its prescribed map to the global quotient. -/
@[reassoc]
lemma baseChartMap_fac (c : BaseChart ρ f) :
    baseChartMap ρ f c ≫ chartMap ρ c.val.1 = c.val.2.val.ι ≫ f :=
  IsOpenImmersion.lift_fac _ _ _

/-- Flatness is inherited by the actual affine chart map. -/
instance baseChartMap_flat [Flat f] (c : BaseChart ρ f) : Flat (baseChartMap ρ f c) := by
  apply MorphismProperty.of_postcomp @Flat (W' := @IsOpenImmersion)
    (baseChartMap ρ f c) (chartMap ρ c.val.1) inferInstance
  rw [baseChartMap_fac]
  infer_instance

/-- Each chosen base chart is affine with its actual structure sheaf. -/
instance baseChart_isAffine (c : BaseChart ρ f) : IsAffine c.val.2.val.toScheme :=
  c.val.2.property

/-- The local source is the scheme pullback of the chosen affine quotient. -/
def baseChartSource (c : BaseChart ρ f) : Scheme.{u} :=
  pullback (quotientMap (action ρ c.val.1)) (baseChartMap ρ f c)

/-- The local source is affine, since all three schemes in its pullback diagram are affine. -/
instance baseChartSource_isAffine (c : BaseChart ρ f) : IsAffine (baseChartSource ρ f c) := by
  unfold baseChartSource
  infer_instance

end FLT.Mazur.StableAffineQuotient
