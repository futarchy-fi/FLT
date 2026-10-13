/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorCoconeMaps
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneInfinity
public import FLT.Mazur.WeierstrassDividedInitialTensorInfinityIntersection
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorCoconeMaps

/-!
# The full start-zero initial and infinity atlas intersection

The entire shifted vertical open in the slope chart is the actual pullback.
No unshifted substitute or condition on the first retained conic is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
set_option maxRecDepth 2048
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨1, by omega⟩
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ 0) = 1 from by simp
local notation "gc" => coefficientShearResidueZeroInitial_coefficients hπ hm data s hs
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "a" => (U).a₁
local notation "P" => SlopeOpen a
local notation "z" => (slopeZ a * (slopeZ a + algebraMap Q P a)) *
  (slopeZ a + algebraMap Q P r)
local notation "y" => WeierstrassModificationX.y W (π ^ 0) (d).b3 (d).b4 (d).b6
local notation "ci" => incidenceCoefficientShearIso W (π ^ 0) (d).b3 (d).b4 (d).b6 Q r
local notation "I" => coefficientShearResidueZeroInitialIso hπ hm data s hs
local notation "e₀" => tensorShearScaleOneEquiv W (π ^ 0) (d).b3 (d).b4 (d).b6
  Q r hscale (gc).1 (gc).2.1 (gc).2.2 hr
local notation "N" => Scheme.Spec.mapIso (e₀).toRingEquiv.toCommRingCatIso.op
local notation "L" => tensorShearScaleOneInfinityIso W (π ^ 0) (d).b3 (d).b4 (d).b6
  Q r hscale (gc).1 (gc).2.1 (gc).2.2 hr
local notation "p" => PrincipalOpenTransport.inclusion z

/-- The full tensor comparison gives the entire initial equation after inverse shear. -/
@[reassoc] theorem coefficientShearResidueZeroInitialIso_tensor :
    (N).hom ≫ (ci).inv = (I).hom := by
  apply (cancel_mono (ci).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

variable [IsBezout R]
local notation "atlas" => coefficientShearAtlasMap hπ data Q r (s + 1) hs

/-- The full shifted slope boundary maps to the original infinity tensor chart. -/
def coefficientShearResidueZeroInfinityBoundary :
    Spec (.of (Localization.Away z)) ⟶
      coefficientShearAtlasObject data Q r (s + 1) hs (.inl 0) :=
  (L).hom ≫ initialGlobalYToInfinity hπ data Q (s + 1) hs
local notation "b" => coefficientShearResidueZeroInfinityBoundary hπ hm data s hs

/-- The entire shifted original vertical open is the actual infinity/initial intersection. -/
theorem coefficientShearResidueZeroInfinityBoundary_isPullback :
    IsPullback b (p ≫ (I).hom) (atlas (.inl 0)) (atlas (.inl 2)) := by
  apply (initialGlobalTensor_infinity_isPullback hπ data Q (s + 1) hs).of_iso'
    L (Iso.refl _) ci (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · rw [tensorShearScaleOneInfinityIso_inclusion]
    have H := coefficientShearResidueZeroInitialIso_tensor hπ hm data s hs
    have H' := congrArg (· ≫ (ci).hom) H
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at H'
    simpa only [Category.assoc] using congrArg (p ≫ ·) H'
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

/-- Both complete atlas projections agree on the actual shifted infinity boundary. -/
@[reassoc] theorem coefficientShearResidueZeroInfinityBoundary_comp :
    b ≫ atlas (.inl 0) = p ≫ (I).hom ≫ atlas (.inl 2) := by
  simpa only [Category.assoc] using
    (coefficientShearResidueZeroInfinityBoundary_isPullback hπ hm data s hs).w

end FLT.Mazur.WeierstrassDividedDepth
