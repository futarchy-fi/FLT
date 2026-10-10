/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentBoundary
public import FLT.Mazur.WeierstrassModificationXConicGeometry
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# Gluing the entire equality-depth terminal component

Glue the original conic and the entire terminal Laurent chart along their
actual incidence open. Both charts remain open and jointly cover. This is
an explicit scheme over the residue field, without a terminal node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) = n)
local notation "K" => ResidueField R
local notation "a" => WeierstrassCurve.a₁ (W.map (residue R))
local notation "c" => residue R b6
local notation "C₀" => ConicCoordinate a c
local notation "B" => MiddleConicOpen (W.map (residue R)) c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "ψ" => residueLaurentConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local instance conicBoundary_open : IsOpenImmersion i :=
  IsOpenImmersion.of_isLocalization (conicT a c)

/-- The two complete original charts glued along their exact incidence open. -/
def laurentConicComponent : Scheme.{u} := pushout i s
local notation "P" => laurentConicComponent D k hk b3 b4 b6 h3 h4 h6 hp

/-- The complete original conic is a chart of the glued terminal component. -/
def laurentConicComponentConic : Spec (.of C₀) ⟶ P := pushout.inl i s

/-- The entire Laurent terminal chart is retained, including its missing conic points. -/
def laurentConicComponentTorus : Spec (.of (K[T;T⁻¹])) ⟶ P := pushout.inr i s
local notation "l" => laurentConicComponentConic D k hk b3 b4 b6 h3 h4 h6 hp
local notation "r" => laurentConicComponentTorus D k hk b3 b4 b6 h3 h4 h6 hp

instance laurentConicComponentConic_open : IsOpenImmersion l := by
  change IsOpenImmersion (colimit.ι (span i s) WalkingSpan.left)
  infer_instance

instance laurentConicComponentTorus_open : IsOpenImmersion r := by
  change IsOpenImmersion (colimit.ι (span i s) WalkingSpan.right)
  infer_instance

/-- The charts identify precisely the specified original conic boundary functions. -/
@[reassoc] theorem laurentConicComponent_condition : i ≫ l = s ≫ r := pushout.condition

/-- Every point lies on the complete conic or on the complete terminal Laurent chart. -/
theorem laurentConicComponent_cover (x : P) : x ∈ Set.range l ∨ x ∈ Set.range r := by
  obtain ⟨j, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span i s) x
  cases j with
  | none =>
    left
    refine ⟨i y, ?_⟩
    change (i ≫ l) y = x
    rw [show i ≫ l = colimit.ι (span i s) WalkingSpan.zero from
      colimit.w (span i s) WalkingSpan.Hom.fst]
    exact hy
  | some j =>
    cases j with
    | left => exact Or.inl ⟨y, hy⟩
    | right => exact Or.inr ⟨y, hy⟩

/-- The glued component carries the original residue-field structure. -/
def laurentConicComponentStructure : P ⟶ Spec (.of K) :=
  pushout.desc (conicStructure a c) (MultiplicativeGroupScheme.gm K).hom (by
    change i ≫ Spec.map _ = s ≫ Spec.map _
    erw [WeierstrassDividedDepth.terminalComponent_algebra_structure
      (Algebra.algHom K C₀ B),
      WeierstrassDividedDepth.terminalComponent_algebra_structure ψ])
local notation "p" => laurentConicComponentStructure D k hk b3 b4 b6 h3 h4 h6 hp

/-- The original conic chart keeps its coefficient morphism. -/
@[reassoc] theorem laurentConicComponentConic_structure : l ≫ p = conicStructure a c :=
  pushout.inl_desc _ _ _

/-- The complete terminal Laurent chart keeps its coefficient morphism. -/
@[reassoc] theorem laurentConicComponentTorus_structure :
    r ≫ p = (MultiplicativeGroupScheme.gm K).hom := pushout.inr_desc _ _ _

/-- The actual two charts characterize every outgoing morphism uniquely. -/
theorem laurentConicComponent_hom_ext {Y : Scheme.{u}} {f g : P ⟶ Y}
    (hl : l ≫ f = l ≫ g) (hr : r ≫ f = r ≫ g) : f = g :=
  pushout.hom_ext hl hr

end FLT.Mazur.WeierstrassSuccessiveX
