/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorOverlap

/-!
# Gluing schemes from independent original selector charts

The actual quotient schemes glue along their proved open transitions.
No global selector, prescribed quotient scheme, or gluing compatibility
of the individual representative choices is part of the input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOpenSelector
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]

/-- Actual scheme gluing data constructed from independent original selector charts. -/
def glueData : Scheme.GlueData.{u} := Scheme.IsLocallyDirected.glueData (diagram p q e)

/-- The full triple-overlap cocycle is a theorem of the constructed gluing data. -/
theorem cocycle (i j k : (glueData e).J) :
    (glueData e).t' i j k ≫ (glueData e).t' j k i ≫ (glueData e).t' k i j = 𝟙 _ :=
  (glueData e).cocycle i j k

/-- A scheme assembled from local representatives, with no globally compatible choices. -/
def glued : Scheme.{u} := colimit (diagram p q e)

/-- Each constructed quotient chart maps to the glued scheme. -/
def chartMap (U : Chart p q) : (selector p q U).quotient ⟶ glued e :=
  colimit.ι (diagram p q e) U

instance chartMap_isOpenImmersion (U : Chart p q) : IsOpenImmersion (chartMap e U) := by
  unfold chartMap
  infer_instance

/-- The original quotient charts constitute an actual scheme open cover. -/
def cover : (glued e).OpenCover := Scheme.IsLocallyDirected.openCover (diagram p q e)

/-- Original source inclusions are respected by the glued quotient chart maps. -/
@[reassoc]
theorem transition_chartMap {U V : Chart p q} (h : U ≤ V) :
    transition p q h ≫ chartMap e V = chartMap e U :=
  colimit.w (diagram p q e) (homOfLE h)

/-- Every point of the constructed scheme comes from a literal original source parameter. -/
theorem exists_original (z : glued e) : ∃ (U : Chart p q) (x : U.val.val.toScheme),
    chartMap e U ((selector p q U).projection x) = z := by
  obtain ⟨U, y, hy⟩ := (cover e).exists_eq z
  obtain ⟨x, rfl⟩ := (selector p q U).projection.surjective y
  exact ⟨U, x, hy⟩

/-- Equality in the glued scheme is witnessed by an actual common original selector chart. -/
theorem chartMap_eq_iff {U V : Chart p q}
    (x : (selector p q U).quotient) (y : (selector p q V).quotient) :
    chartMap e U x = chartMap e V y ↔
      ∃ (W : Chart p q) (hU : W ≤ U) (hV : W ≤ V)
        (z : (selector p q W).quotient),
        transition p q hU z = x ∧ transition p q hV z = y := by
  change colimit.ι (diagram p q e) U x = colimit.ι (diagram p q e) V y ↔ _
  rw [Scheme.IsLocallyDirected.ι_eq_ι_iff]
  constructor
  · rintro ⟨W, hU, hV, z, hx, hy⟩
    exact ⟨W, leOfHom hU, leOfHom hV, z, hx, hy⟩
  · rintro ⟨W, hU, hV, z, hx, hy⟩
    exact ⟨W, homOfLE hU, homOfLE hV, z, hx, hy⟩

end FLT.Mazur.SchemeRelationOpenSelector
