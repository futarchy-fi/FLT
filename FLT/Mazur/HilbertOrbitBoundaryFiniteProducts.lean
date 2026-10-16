/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOrbitBoundaryFiniteOriginalLift

/-!
# Original boundary coefficients of finite chart power products

The exact product boundary equation is detected on the selected finite fppf
cover. It remains an equation on the unchanged original boundary sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.SchemeFppfFamily
/-- Multiplying chart lifts by an original power preserves exact boundary coefficients. -/
theorem boundary_power_of_chart_tests {X Y : Scheme.{0}}
    (C : Scheme.Cover.{0} Scheme.fppfPrecoverage X) (g : Y ⟶ X)
    (r s : Γ(X, ⊤)) (t : Γ(Y, ⊤)) (N : ℕ) (u v : ∀ a, Γ(C.X a, ⊤))
    (hr : ∀ a, (C.f a).appTop r = u a)
    (hs : ∀ a, (C.f a).appTop s = u a ^ N * v a)
    (ht : ∀ (T : Scheme.{0}) (a : C.I₀) (x : T ⟶ C.X a) (y : T ⟶ Y),
      x ≫ C.f a = y ≫ g → x.appTop (v a) = y.appTop t) :
    g.appTop s = g.appTop r ^ N * t := by
  apply boundary_eq_of_chart_tests C g
  intro T a x y hxy
  rw [hs]
  have he : x.appTop (u a) = y.appTop (g.appTop r) := by
    rw [← hr]
    simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop]
    exact congrArg (fun morphism ↦ morphism.appTop r) hxy
  simp only [map_mul, map_pow, he, ht T a x y hxy]
end FLT.Mazur.SchemeFppfFamily

namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
attribute [local irreducible] relation fst snd equivalence
  EquivalenceRelationNormalizedFrames.source
namespace OrbitBoundaryAtlas.FiniteAtlas
attribute [local irreducible] finiteCharts lifts obstruction
local notation "e" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen e W).val

variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
local notation "C" => finiteCharts f hL d V c k W hW

local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k
local notation "hp" => originalClosedArrow_fst f hL d V c k
local notation "hq" => originalClosedArrow_snd f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Ec" => (pullOpen ec Wc).val
local notation "g" => (openSourceMap e ec i z hp hq W).left
attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence InvariantBoundary.boundary
attribute [local irreducible] RelativeRelationOrbit.openSourceMap
  InvariantOpenRelationDiagram.sourceMap InvariantOpenRelationDiagram.orbitFunctions

variable (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
  (op ((TopologicalSpace.Opens.map (originalClosedInvariantMap f hL d V c k).base).obj W)))

local notation "φ" => originalClosedSectionPullback f hL d V c k W

omit [IsAffine V.left] in
/-- Naturality computes the full original boundary coefficient of a scalar power product. -/
theorem original_power_value (a : (invariantSheaf e).obj.obj (op W)) (N : ℕ) :
    (orbitFunctions ec Wc (φ a ^ N * t)).val =
      (fun coeff : Γ((Ec).toScheme, ⊤) ↦
        coeff ^ N * (show Γ((Ec).toScheme, ⊤) from (orbitFunctions ec Wc t).val))
          ((g).appTop (orbitFunctions e W a).val) := by
  have hn : (orbitFunctions ec Wc (φ a)).val = (g).appTop (orbitFunctions e W a).val :=
    (congrArg Subtype.val (openFunctionMap_natural e ec i z hp hq W a)).symm
  have hproduct : (orbitFunctions ec Wc (φ a ^ N * t)).val =
      (orbitFunctions ec Wc (φ a)).val ^ N * (orbitFunctions ec Wc t).val := by
    simp only [map_mul, map_pow]
    rfl
  have hm := congrArg (fun coeff : Γ((Ec).toScheme, ⊤) ↦
    coeff ^ N * (show Γ((Ec).toScheme, ⊤) from (orbitFunctions ec Wc t).val)) hn
  exact hproduct.trans hm

/-- Multiplication of exact boundary lifts retains the original scalar boundary coefficient. -/
theorem descended_power_boundary (u v : Sections f hL d V c k W hW)
    (hvBoundary : ∀ j : C,
      normalizedBoundaryChartMap f hL d V c k j.val.size j.val.label j.val.domain j.val.stable
        (v j) = normalizedOrbitBoundaryCoefficient f hL d V c k j.val.size j.val.label W
          j.val.domain j.val.stable j.val.overDomain t)
    (a b : (invariantSheaf e).obj.obj (op W)) (N : ℕ)
    (ha : ∀ j : C, (chartMap f hL d V c k W j.val).appTop
      (orbitFunctions e W a).val = (u j).val)
    (hb : ∀ j : C, (chartMap f hL d V c k W j.val).appTop
      (orbitFunctions e W b).val = (u j).val ^ N * (v j).val) :
    (g).appTop (orbitFunctions e W b).val =
      (orbitFunctions ec Wc ((φ a) ^ N * t)).val := by
  have hs := SchemeFppfFamily.boundary_power_of_chart_tests
    (finiteFppfCover f hL d V c k W hW) g
    (orbitFunctions e W a).val (orbitFunctions e W b).val (orbitFunctions ec Wc t).val N
    (fun j ↦ (u j).val) (fun j ↦ (v j).val) ha hb
    (fun T j x y hxy ↦ boundary_chart_test f hL d V c k W hW t v j
      (hvBoundary j) x y hxy)
  exact hs.trans (original_power_value f hL d V c k W t a N).symm

omit [IsAffine V.left] in
/-- The detected source equation is the actual original boundary lifting equation. -/
theorem original_boundary_power (a b : (invariantSheaf e).obj.obj (op W)) (N : ℕ)
    (hb : (g).appTop (orbitFunctions e W b).val =
      (orbitFunctions ec Wc ((φ a) ^ N * t)).val) : φ b = φ a ^ N * t := by
  apply (orbitFunctions ec Wc).injective
  apply Subtype.ext
  have hn : (orbitFunctions ec Wc (φ b)).val = (g).appTop (orbitFunctions e W b).val :=
    (congrArg Subtype.val (openFunctionMap_natural e ec i z hp hq W b)).symm
  exact hn.trans hb

end OrbitBoundaryAtlas.FiniteAtlas
end FLT.Mazur.HilbertChart.AffineRestriction
