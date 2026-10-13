/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroFirstCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroLengthTwoCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroRetainedCoconeMaps

/-!
# The full first retained incidence line for every start-zero chain

The same exterior restriction holds for the zero and nonzero original conic constants.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n)
  (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)
    (Nat.zero_lt_succ (2 * s + 1)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

open WeierstrassModificationX WeierstrassSuccessiveX
local notation "e" => data ⟨1, by omega⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ (0 + 0)) = 1 from by simp
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "E" => coefficientShearRetainedScaleOneTensorIso
  data Q r (s + 1) hs ⟨0, Nat.zero_lt_succ s⟩
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap
  W (π ^ (0 + 0)) π (e).b3 (e).b4 (e).b6 Q r hscale hp (lin).1 (lin).2 hr).toRingHom)
local notation "D" => coefficientShearResidueZeroAtlasCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C

/-- The full original incidence line always receives the same exterior component. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_first_exterior :
    L ≫ (E).inv ≫ D (.inr ⟨0, Nat.zero_lt_succ s⟩) =
      ProjectiveLine.left Q ≫ (ProjectiveLine.slopeNormalizationIso a).hom ≫ F 0 := by
  rw [coefficientShearResidueZeroAtlasCoconeMap_retained]
  by_cases hs0 : s = 0
  · subst s
    rw [coefficientShearResidueZeroRetainedCoconeMap]
    simp only [↓reduceDIte]
    exact coefficientShearResidueZeroLengthTwoCoconeDesc_exterior
      hπ hm data hs he h3 h4 h6next hc C
  · rw [coefficientShearResidueZeroRetainedCoconeMap_first
      hπ hm data s hs he h3 h4 h6next hc C (Nat.pos_of_ne_zero hs0)]
    exact coefficientShearResidueZeroFirstCoconeDesc_exterior
      hπ hm data s hs (Nat.pos_of_ne_zero hs0) h3 h4 hc C

end FLT.Mazur.WeierstrassDividedDepth
