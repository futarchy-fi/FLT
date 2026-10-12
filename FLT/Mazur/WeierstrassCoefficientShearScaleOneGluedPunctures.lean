/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneGluedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearScaleOneGluedConic

/-!
# Full signed conic punctures in the actual adjacent gluing

Each equality keeps the original complete conic map and the actual next
retained line, with the signed reciprocal automorphism between parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)
include hj hjNext
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "e" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
variable (hs : algebraMap R S (π ^ (start + j)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
include h3 h4
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "hsNext" => coefficientShearAdjacent_scale S hp (k := start + j)
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e S hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e S hp))
local notation "c" => algebraMap R S (Data.b6 d)
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial S →+* S[T;T⁻¹]))

variable (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "b₁" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundaryFirst U c hu gc)))
local notation "b₂" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundarySecond U c hu gc)))
local notation "ρ₁" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv (a⁻¹)))))
local notation "ρ₂" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (PolygonScaledReciprocal.equiv ((-a)⁻¹)))))
local notation "conic" => tensorShearScaleOneConicImmersion W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp g3 g4 hr ≫
    coefficientShearRetainedTensorChart hπ data S r (j + 2 + m) hm (Fin.mk j (by omega))
local notation "inc" => PrincipalOpenTransport.inclusion
  (conicT (WeierstrassCurve.a₁ U) c)
local notation "line" => coefficientShearRetainedLine hπ data S r (j + 2 + m) hm
  (Fin.mk (j + 1) (by omega)) hsNext hp h3 h4 hr

local notation "P₁" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicPuncturedFirst U c gc)))
local notation "P₂" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicPuncturedSecond U c gc)))

include ha in
/-- The complete positive conic puncture is the signed reciprocal next-line map. -/
theorem coefficientShearScaleOneFirst_gluedPuncture :
    P₁ ≫ conic = (ρ₁).hom ≫ p ≫ line 0 (middle_first_root U) := by
  have h := (coefficientShearScaleOneAdjacentGluedFirstFull_isPullback
    hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha).w
  have hb : b₁ ≫ inc = P₁ := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (conicBoundaryFirst_base U c hu gc)
  rw [hb] at h
  exact h.trans (Category.assoc _ _ _)

include ha in
/-- The opposite puncture keeps the negative reciprocal and the opposite actual line. -/
theorem coefficientShearScaleOneSecond_gluedPuncture :
    P₂ ≫ conic = (ρ₂).hom ≫ p ≫ line (-(U).a₁) (middle_second_root U) := by
  have h := (coefficientShearScaleOneAdjacentGluedSecondFull_isPullback
    hπ data S r j hj hjNext m hm hs hp h3 h4 hr a ha).w
  have hb : b₂ ≫ inc = P₂ := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (conicBoundarySecond_base U c hu gc)
  rw [hb] at h
  exact h.trans (Category.assoc _ _ _)

end FLT.Mazur.WeierstrassDividedDepth
