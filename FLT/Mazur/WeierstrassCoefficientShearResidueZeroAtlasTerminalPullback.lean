/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasTerminalBoundary
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasTerminalBoundary
public import FLT.Mazur.WeierstrassCoefficientShearTerminalAtlasPullback
public import FLT.Mazur.WeierstrassCoefficientShearRetainedEqualityBoundaryDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroRetainedCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroTerminalDescent

/-!
# Start-zero positive terminal cocone compatibility on the full terminal atlas pullback

The explicit terminal boundary exhausts the scheme-theoretic atlas intersection,
so its compatibility gives the required gluing equation on the full pullback.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (hspos : 0 < s)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "d" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)
    (Nat.zero_lt_succ (2 * s + 1)))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 2)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 2) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 2) (by omega) C.inl C.inr C.condition i

local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_eq he) h3 h4
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm d he h6next
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < 0 + s from by omega)
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "h2" => coefficientShear_a₂_zero W Q r hr
local notation "hsNext" => show algebraMap R Q (π ^ (0 + (s + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "e" => coefficientShearLaurentEquiv W (π ^ (0 + (s + 1)))
  (d).b3 (d).b4 (d).b6 Q r hsNext (lin).1 (lin).2 hr a ha cunit
local notation "L" => Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "I" => coefficientShearRetainedEquationIso data Q r (s + 1) hs
  ⟨s, Nat.lt_succ_self s⟩ hscale hp (lin).1 (lin).2
local notation "q" => coefficientShearEqualityConicParameter
  data Q r s hs hscale hp (lin).1 (lin).2 cunit hr a ha
local notation "ψ" => tensorShearTerminalLaurentConicMap W π (0 + s)
  (d).b3 (d).b4 (d).b6 Q r hscale hp (lin).1 (lin).2 hr cunit a ha
local notation "b" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "inc" => PrincipalOpenTransport.inclusion (conicT (U).a₁ c)
local notation "ρ" => ProjectiveLine.endpointReversal Q
local notation "D" => coefficientShearResidueZeroAtlasCoconeMap
  hπ hm data s hs he h3 h4 h6next hc C

local notation "A" => coefficientShearAtlasMap hπ data Q r (s + 1) hs
local notation "last" => Sum.inr (Fin.mk s (Nat.lt_succ_self s))
local notation "P" => coefficientShearTerminalAtlasPullbackIso
  hπ data Q r s hs hscale hp (lin).1 (lin).2 cunit hr a ha

include hspos

/-- Actual cocone descent agrees on the entire terminal pairwise atlas intersection. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_terminal_pullback :
    pullback.fst (A (.inl 1)) (A last) ≫ D (.inl 1) =
      pullback.snd (A (.inl 1)) (A last) ≫ D last := by
  apply (cancel_epi (P).hom).mp
  simp only [← Category.assoc, coefficientShearTerminalAtlasPullbackIso_fst,
    coefficientShearTerminalAtlasPullbackIso_snd]
  simpa only [Category.assoc] using
    (coefficientShearResidueZeroAtlasCoconeMap_terminal_boundary
      hπ hm data s hs he hspos h3 h4 h6next hc C).symm

/-- The reverse ordered pair has the same complete pullback compatibility. -/
theorem coefficientShearResidueZeroAtlasCoconeMap_terminal_pullback_symm :
    pullback.fst (A last) (A (.inl 1)) ≫ D last =
      pullback.snd (A last) (A (.inl 1)) ≫ D (.inl 1) := by
  apply (cancel_epi (pullbackSymmetry (A (.inl 1)) (A last)).hom).mp
  simpa only [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
    using (coefficientShearResidueZeroAtlasCoconeMap_terminal_pullback
      hπ hm data s hs he hspos h3 h4 h6next hc C).symm

end FLT.Mazur.WeierstrassDividedDepth
