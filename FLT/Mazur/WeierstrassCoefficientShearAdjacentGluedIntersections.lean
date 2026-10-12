/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

public import FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedFullConic
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentGluedFullConic

/-!
# Both signed adjacent intersections at every retained depth

Each complete Laurent puncture is the scheme intersection of the whole
preceding conic and the actual next retained tangent line in the gluing.
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
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
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
local notation "conic" => coefficientShearRetainedConic hπ data S r (j + 2 + m) hm
  (Fin.mk j (by omega)) hs hp g3 g4 hr
local notation "inc" => PrincipalOpenTransport.inclusion
  (conicT (WeierstrassCurve.a₁ U) c)
local notation "line" => coefficientShearRetainedLine hπ data S r (j + 2 + m) hm
  (Fin.mk (j + 1) (by omega)) hsNext hp h3 h4 hr

set_option maxHeartbeats 600000 in
-- Indexed component presentations require additional elaboration heartbeats.
/-- The full preceding conic and the entire first line have this signed intersection. -/
theorem coefficientShearAdjacentGluedFirstFull_isPullback :
    IsPullback (b₁ ≫ inc) ((ρ₁).hom ≫ p) conic (line 0 (middle_first_root U)) := by
  have sq := coefficientShearAdjacentFirst_isPullback hπ d e S r hs hp h3 h4 hr a ha
  rw [← coefficientShearAdjacentConicToNext_def] at sq
  have full := coefficientShearAdjacentGluedFullConic_isPullback hπ data S r j hj hjNext
    m hm hs hp hr
  rw [← coefficientShearRetainedTensorChart_line]
  exact sq.paste_horiz full.flip

set_option maxHeartbeats 600000 in
-- Indexed component presentations require additional elaboration heartbeats.
/-- The full preceding conic and the entire second line have this signed intersection. -/
theorem coefficientShearAdjacentGluedSecondFull_isPullback :
    IsPullback (b₂ ≫ inc) ((ρ₂).hom ≫ p) conic (line (-(U).a₁) (middle_second_root U)) := by
  have sq := coefficientShearAdjacentSecond_isPullback hπ d e S r hs hp h3 h4 hr a ha
  rw [← coefficientShearAdjacentConicToNext_def] at sq
  have full := coefficientShearAdjacentGluedFullConic_isPullback hπ data S r j hj hjNext
    m hm hs hp hr
  rw [← coefficientShearRetainedTensorChart_line]
  exact sq.paste_horiz full.flip

end FLT.Mazur.WeierstrassDividedDepth
