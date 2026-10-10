/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentComponent
public import FLT.Mazur.SchemeOpenPushoutIntersection

/-!
# Smoothness and the full chart intersection of the equality-depth component

Smoothness is proved on the two original complete charts. The glued component
has their exact incidence intersection; no terminal node is introduced.
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
local notation "P" => laurentConicComponent D k hk b3 b4 b6 h3 h4 h6 hp
local notation "l" => laurentConicComponentConic D k hk b3 b4 b6 h3 h4 h6 hp
local notation "r" => laurentConicComponentTorus D k hk b3 b4 b6 h3 h4 h6 hp
local notation "p" => laurentConicComponentStructure D k hk b3 b4 b6 h3 h4 h6 hp
local instance laurentSmoothConicBoundary_open : IsOpenImmersion i :=
  IsOpenImmersion.of_isLocalization (conicT a c)

/-- The two entire charts have precisely the original incidence fiber product. -/
theorem laurentConicComponent_isPullback : IsPullback i s l r :=
  SchemeOpenPushout.isPullback i s

/-- Equality-depth gluing is smooth at every point, including the original attachments. -/
theorem laurentConicComponentStructure_smooth : Smooth p := by
  let _ := conicStructure_smooth a c (D.a₁_unit.map (residue R))
  let _ := MultiplicativeGroupScheme.smooth K
  apply IsZariskiLocalAtSource.of_openCover (Scheme.IsLocallyDirected.openCover (span i s))
  intro j
  cases j with
  | none =>
    change Smooth (colimit.ι (span i s) WalkingSpan.zero ≫ p)
    rw [← colimit.w (span i s) WalkingSpan.Hom.fst]
    change Smooth ((i ≫ l) ≫ p)
    rw [Category.assoc, laurentConicComponentConic_structure]
    infer_instance
  | some j =>
    cases j with
    | left =>
      change Smooth (l ≫ p)
      rw [laurentConicComponentConic_structure]
      infer_instance
    | right =>
      change Smooth (r ≫ p)
      rw [laurentConicComponentTorus_structure]
      infer_instance

omit [IsDomain R] in
include D h6 hp in
/-- The original conic constant is a unit at equality depth. -/
theorem laurentConicComponent_constant_isUnit : IsUnit c :=
  (WeierstrassDilatation.divided_constant_isUnit D (k + 1) hp b6 h6).map (residue R)

omit [IsDomain R] in
include D h6 hp in
/-- In particular this component never uses the vanishing-constant split conic. -/
theorem laurentConicComponent_constant_ne_zero : c ≠ 0 :=
  (laurentConicComponent_constant_isUnit D k b6 h6 hp).ne_zero

end FLT.Mazur.WeierstrassSuccessiveX
