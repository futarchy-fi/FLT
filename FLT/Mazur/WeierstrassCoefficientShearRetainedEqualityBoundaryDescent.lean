/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearEqualityChartParameters
public import FLT.Mazur.WeierstrassCoefficientShearRetainedEqualityDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEqualityDescent

/-!
# Descent compatibility on the entire original terminal boundary

The original localized conic-to-Laurent transition preserves the completed parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "ψ" => tensorShearTerminalLaurentConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)

local notation "l" => WeierstrassSuccessiveShearTerminal.laurentConicComponentConic
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "t" => WeierstrassSuccessiveShearTerminal.laurentConicComponentTorus
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "J" => WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha


local notation "q" => coefficientShearEqualityConicParameter
  data S r j hj hs hp h3 h4 hc hr a ha
local notation "v" => coefficientShearEqualityDividedParameter
  data S r j hj hp h3 h4 hc hr a ha

/-- The entire original localized conic boundary has the same completed projective parameter. -/
@[reassoc] theorem coefficientShearEqualityConicParameter_boundary :
    inc ≫ q = b ≫ ProjectiveLine.overlapLeft S ≫ ProjectiveLine.left S := by
  apply (cancel_mono (J).hom).mp
  rw [coefficientShearEqualityConicParameter]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso_torus]
  exact pushout.condition

local notation "e" => coefficientShearLaurentEquiv W (π ^ (start + (j + 1)))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hsNext h3 h4 hr a ha hc
local notation "L" => Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "E" => coefficientShearRetainedEquationIso data S r (j + 1) hj
  ⟨j, Nat.lt_succ_self j⟩ hs hp h3 h4
local notation "h2" => coefficientShear_a₂_zero W S r hr
variable {Y : Scheme.{u}} (f g₁ g₂ : ProjectiveLine.scheme S ⟶ Y)
  (w₁ : ProjectiveLine.zero S ≫ f = ProjectiveLine.infinity S ≫ g₁)
  (w₂ : ProjectiveLine.infinity S ≫ f = ProjectiveLine.infinity S ≫ g₂)
local notation "D" => coefficientShearRetainedEqualityDesc
  data S r j hj hs hp h3 h4 hc hr a ha f g₁ g₂ w₁ w₂

/-- Retained and divided descent agree on the whole original conic-Laurent boundary. -/
theorem coefficientShearRetainedEqualityDesc_boundary :
    inc ≫ middleConicImmersion U c h2 ≫ (E).hom ≫ D = b ≫ (L).hom ≫ v ≫ f := by
  have H := congrArg (fun m => inc ≫ m)
    (coefficientShearRetainedEqualityDesc_conic
      data S r j hj hs hp h3 h4 hc hr a ha f g₁ g₂ w₁ w₂)
  have H' := congrArg (fun m => b ≫ m ≫ f)
    (coefficientShearEqualityDividedParameter_laurent data S r j hj hp h3 h4 hc hr a ha)
  calc
    _ = inc ≫ q ≫ f := by simpa only [Category.assoc] using H
    _ = b ≫ ProjectiveLine.overlapLeft S ≫ ProjectiveLine.left S ≫ f :=
      coefficientShearEqualityConicParameter_boundary_assoc
        data S r j hj hs hp h3 h4 hc hr a ha f
    _ = _ := by simpa only [Category.assoc] using H'.symm

end FLT.Mazur.WeierstrassDividedDepth
