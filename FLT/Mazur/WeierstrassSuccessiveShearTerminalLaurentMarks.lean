/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentComponent
public import FLT.Mazur.WeierstrassModificationXConicParameterSections

/-!
# The original ordered attachments on the equality-depth component

Both full conic parameter opens and their original origins are retained on
the glued component, with their coefficient structures and tangent order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveShearTerminal
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [Field S] [Algebra R S] (ρ : S)
  (hs : algebraMap R S (π ^ k) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : ρ ^ 2 + algebraMap R S W.a₁ * ρ - algebraMap R S W.a₂ = 0)
  (hc : IsUnit (algebraMap R S b6)) (u : Sˣ)
  (hu : (u : S) = (rootShearCurve (W.map (algebraMap R S)) ρ).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) ρ
local notation "K" => S
local notation "a" => WeierstrassCurve.a₁ U
local notation "c" => algebraMap R S b6
local notation "ha" => Eq.mp (congrArg IsUnit hu) (Units.isUnit u)
local notation "C₀" => ConicCoordinate a c
local notation "B" => MiddleConicOpen U c
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap C₀ B))
local notation "ψ" => tensorShearTerminalLaurentConicMap W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "P" => laurentConicComponent W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "l" => laurentConicComponentConic W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "r" => laurentConicComponentTorus W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu
local notation "p" => laurentConicComponentStructure W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu

/-- The entire original first conic parameter open in the glued component. -/
def laurentConicComponentFirstParameter : Spec (.of (ConicParameterOpen c)) ⟶ P :=
  (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫ l

/-- The first original conic marking, without introducing a terminal node. -/
def laurentConicComponentFirstSection : Spec (.of K) ⟶ P :=
  Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) ≫ l

/-- The full first parameter keeps its original incidence origin. -/
@[reassoc] theorem laurentConicComponentFirstParameter_origin :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      laurentConicComponentFirstParameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu =
        laurentConicComponentFirstSection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu := by
  rw [laurentConicComponentFirstParameter, conicFirstParameterIso_origin_assoc]
  rfl

/-- The first original attachment is a section over the coefficient field. -/
@[reassoc] theorem laurentConicComponentFirstSection_structure :
    laurentConicComponentFirstSection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu ≫ p = 𝟙 _ := by
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
      laurentConicComponentSecondParameter W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu =
        laurentConicComponentSecondSection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu := by
  rw [laurentConicComponentSecondParameter, conicSecondParameterIso_origin_assoc]
  rfl

/-- The second original attachment is a section over the coefficient field. -/
@[reassoc] theorem laurentConicComponentSecondSection_structure :
    laurentConicComponentSecondSection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu ≫ p = 𝟙 _ := by
  rw [laurentConicComponentSecondSection, Category.assoc,
    laurentConicComponentConic_structure]
  change Spec.map _ ≫ Spec.map _ = _
  rw [WeierstrassDividedDepth.terminalComponent_algebra_structure
    (conicSecondIncidencePoint a c ha)]
  exact Spec.map_id _

/-- The two original attachments remain distinct on the entire glued component. -/
theorem laurentConicComponentSections_ne :
    laurentConicComponentFirstSection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu ≠
      laurentConicComponentSecondSection W π k b3 b4 b6 S ρ hs hp h3 h4 hr hc u hu := by
  intro h
  have h' := (cancel_mono l).mp h
  have hv := congrArg (fun f => f.hom (conicV a c)) (Spec.map_injective h')
  change conicFirstIncidencePoint a c ha (conicV a c) =
    conicSecondIncidencePoint a c ha (conicV a c) at hv
  rw [conicFirstIncidencePoint_v, conicSecondIncidencePoint_v] at hv
  exact (ha).ne_zero (neg_eq_zero.mp hv.symm)

end FLT.Mazur.WeierstrassSuccessiveShearTerminal
