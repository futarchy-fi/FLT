/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalLaurentComponent
public import FLT.Mazur.WeierstrassModificationXConicParameterSections

/-!
# The original ordered attachments on the equality-depth component

Both full conic parameter opens and their original origins are retained on
the glued component, with their coefficient structures and tangent order.
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
local notation "ha" => D.a₁_unit.map (residue R)

/-- The entire original first conic parameter open in the glued component. -/
def laurentConicComponentFirstParameter : Spec (.of (ConicParameterOpen c)) ⟶ P :=
  (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫ l

/-- The first original conic marking, without introducing a terminal node. -/
def laurentConicComponentFirstSection : Spec (.of K) ⟶ P :=
  Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) ≫ l

/-- The full first parameter keeps its original incidence origin. -/
@[reassoc] theorem laurentConicComponentFirstParameter_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      laurentConicComponentFirstParameter D k hk b3 b4 b6 h3 h4 h6 hp =
        laurentConicComponentFirstSection D k hk b3 b4 b6 h3 h4 h6 hp := by
  rw [laurentConicComponentFirstParameter, conicFirstParameterIso_origin_assoc]
  rfl

/-- The first original attachment is a section over the original residue field. -/
@[reassoc] theorem laurentConicComponentFirstSection_structure :
    laurentConicComponentFirstSection D k hk b3 b4 b6 h3 h4 h6 hp ≫ p = 𝟙 _ := by
  rw [laurentConicComponentFirstSection, Category.assoc,
    laurentConicComponentConic_structure]
  change Spec.map _ ≫ Spec.map _ = _
  rw [WeierstrassDividedDepth.terminalComponent_algebra_structure
    (conicFirstIncidencePoint a c ha)]
  exact Spec.map_id _

/-- The entire original second conic parameter open in the glued component. -/
def laurentConicComponentSecondParameter : Spec (.of (ConicParameterOpen c)) ⟶ P :=
  (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫ l

/-- The second original conic marking, without introducing a terminal node. -/
def laurentConicComponentSecondSection : Spec (.of K) ⟶ P :=
  Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) ≫ l

/-- The full second parameter keeps its original incidence origin. -/
@[reassoc] theorem laurentConicComponentSecondParameter_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      laurentConicComponentSecondParameter D k hk b3 b4 b6 h3 h4 h6 hp =
        laurentConicComponentSecondSection D k hk b3 b4 b6 h3 h4 h6 hp := by
  rw [laurentConicComponentSecondParameter, conicSecondParameterIso_origin_assoc]
  rfl

/-- The second original attachment is a section over the original residue field. -/
@[reassoc] theorem laurentConicComponentSecondSection_structure :
    laurentConicComponentSecondSection D k hk b3 b4 b6 h3 h4 h6 hp ≫ p = 𝟙 _ := by
  rw [laurentConicComponentSecondSection, Category.assoc,
    laurentConicComponentConic_structure]
  change Spec.map _ ≫ Spec.map _ = _
  rw [WeierstrassDividedDepth.terminalComponent_algebra_structure
    (conicSecondIncidencePoint a c ha)]
  exact Spec.map_id _

/-- The two original attachments remain distinct on the entire glued component. -/
theorem laurentConicComponentSections_ne :
    laurentConicComponentFirstSection D k hk b3 b4 b6 h3 h4 h6 hp ≠
      laurentConicComponentSecondSection D k hk b3 b4 b6 h3 h4 h6 hp := by
  intro h
  have h' := (cancel_mono l).mp h
  have hv := congrArg (fun f => f.hom (conicV a c)) (Spec.map_injective h')
  change conicFirstIncidencePoint a c ha (conicV a c) =
    conicSecondIncidencePoint a c ha (conicV a c) at hv
  rw [conicFirstIncidencePoint_v, conicSecondIncidencePoint_v] at hv
  exact (ha).ne_zero (neg_eq_zero.mp hv.symm)

end FLT.Mazur.WeierstrassSuccessiveX
