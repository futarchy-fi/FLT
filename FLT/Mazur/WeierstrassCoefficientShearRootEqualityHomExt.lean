/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootEqualityComponent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# The complete equality component detects both original terminal charts

Its completed conic and Laurent torus retain the entire last retained conic and
the whole divided equation. Equality holds for arbitrary target schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
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
local notation "conic" => coefficientShearRetainedConic hπ data S r (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j)) hs hp h3 h4 hr
local notation "N" => coefficientShearTerminalLaurent
  hπ data S r (j + 1) hj hsNext h3 h4 hc hr a ha
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "ψ" => tensorShearTerminalLaurentConicMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "F" => tensorShearConicBoundaryIso W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "T" => tensorShearTerminalLaurentEquiv W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr hc a ha

local notation "P" => WeierstrassSuccessiveShearTerminal.laurentConicComponent
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "l" => WeierstrassSuccessiveShearTerminal.laurentConicComponentConic
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "t" => WeierstrassSuccessiveShearTerminal.laurentConicComponentTorus
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "p" => WeierstrassSuccessiveShearTerminal.laurentConicComponentStructure
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "J" => WeierstrassSuccessiveShearTerminal.laurentConicComponentProjectiveIso
  W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr hc a ha
local notation "g" => coefficientShearGluedStructure hπ data S r (j + 1) hj

local notation "M" => coefficientShearRootLaurentComponentMap
  hπ data S r j hj hs hp h3 h4 hc hr a ha
local notation "C" => coefficientShearRootEqualityComponent
  hπ data S r j hj hs hp h3 h4 hc hr a ha
variable {Y : Scheme.{u}} (u v : coefficientShearGlued hπ data S r (j + 1) hj ⟶ Y)

/-- The complete equality component detects every function on the last retained conic. -/
theorem coefficientShearRootEqualityConic_hom_ext (h : C ≫ u = C ≫ v) :
    conic ≫ u = conic ≫ v := by
  have H : M ≫ u = M ≫ v := by
    apply (cancel_epi (J).hom).mp
    simpa only [coefficientShearRootEqualityComponent, Category.assoc] using h
  have H' := congrArg (fun q => l ≫ q) H
  simpa only [coefficientShearRootLaurentComponentMap_conic_assoc] using H'

/-- The same complete component determines maps on the entire divided atlas chart. -/
theorem coefficientShearRootEqualityDividedChart_hom_ext (h : C ≫ u = C ≫ v) :
    coefficientShearGluedChart hπ data S r (j + 1) hj (.inl 1) ≫ u =
      coefficientShearGluedChart hπ data S r (j + 1) hj (.inl 1) ≫ v := by
  have H := congrArg (fun q => ProjectiveLine.overlapLeft S ≫ ProjectiveLine.left S ≫ q) h
  rw [coefficientShearRootEqualityComponent_torus_assoc,
    coefficientShearRootEqualityComponent_torus_assoc] at H
  unfold coefficientShearTerminalLaurent at H
  rw [Category.assoc, Category.assoc] at H
  exact (cancel_epi _).mp H

end FLT.Mazur.WeierstrassDividedDepth
