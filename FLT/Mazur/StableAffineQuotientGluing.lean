/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientOverlap

/-!
# Gluing the actual affine quotient schemes

The proved local directedness and open-immersion transition maps construct
scheme gluing data, including the full pullback cocycle. Its colimit is
covered by the actual invariant-coordinate quotient charts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.SchemeFiniteGroupQuotient

namespace FLT.Mazur.StableAffineQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [X.IsSeparated]
variable (ρ : G →* Aut X)

/-- Scheme gluing data constructed from the diagram of actual affine quotients. -/
def glueData : Scheme.GlueData.{u} := Scheme.IsLocallyDirected.glueData (diagram ρ)

/-- The transition maps satisfy the full scheme pullback cocycle. -/
theorem glueData_cocycle (i j k : (glueData ρ).J) :
    (glueData ρ).t' i j k ≫ (glueData ρ).t' j k i ≫ (glueData ρ).t' k i j = 𝟙 _ :=
  (glueData ρ).cocycle i j k

/-- The scheme obtained by gluing all actual invariant affine quotients. -/
def glued : Scheme.{u} := colimit (diagram ρ)

/-- The actual quotient chart maps into the glued scheme. -/
def chartMap (U : Chart ρ) : quotient (action ρ U) ⟶ glued ρ := colimit.ι (diagram ρ) U

/-- Each actual quotient chart is an open subscheme of the gluing. -/
instance chartMap_isOpenImmersion (U : Chart ρ) : IsOpenImmersion (chartMap ρ U) := by
  unfold chartMap
  infer_instance

/-- The quotient charts form an actual scheme open cover. -/
def gluedCover : (glued ρ).OpenCover := Scheme.IsLocallyDirected.openCover (diagram ρ)

/-- Quotient chart maps agree along all actual invariant affine inclusions. -/
@[reassoc]
lemma inclusion_chartMap {U V : Chart ρ} (h : U ≤ V) :
    inclusion ρ h ≫ chartMap ρ V = chartMap ρ U :=
  colimit.w (diagram ρ) (homOfLE h)

/-- Every point of the glued scheme is represented in an actual quotient chart. -/
theorem exists_chartMap (x : glued ρ) : ∃ (U : Chart ρ) (y : quotient (action ρ U)),
    chartMap ρ U y = x := (gluedCover ρ).exists_eq x

end FLT.Mazur.StableAffineQuotient
