/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TorusRootsOfUnitySubgroup
public import FLT.Mazur.RootsOfUnityCartier
public import FLT.Mazur.CartierSupportOpenDescent
public import FLT.Mazur.GeneralizedCurveSmoothPullback

/-!
# Cartier roots-of-unity divisors on full toric generalized curves

The actual closed subgroup ideal restricts to the roots-of-unity Cartier
ideal on the torus. Its full support lies there, so the divisor is relative
Cartier on the entire curve, including the singular boundary.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.GeneralizedEllipticCurve

variable {R : Type} [CommRing R] (E : GeneralizedEllipticCurve (Spec (.of R)))
  (e : MultiplicativeGroupScheme.gm R ≅ E.group) [IsMonHom e.hom]
  (n : ℕ) [NeZero n]

local notation "H" => E.torusRootsOfUnitySubgroup e n

/-- Pulling the full subgroup ideal back to its original torus gives the original root ideal. -/
theorem torusRootsOfUnitySubgroup_ideal_on_torus :
    (H).ideal.comap (e.hom.left ≫ E.inclusion.left) = RootsOfUnityCartier.ideal R n := by
  let j := e.hom.left ≫ E.inclusion.left
  let i := (RootsOfUnityScheme.inclusion R n).left
  let _ : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let _ : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (e.hom.left ≫ E.inclusion.left))
  let _ : IsClosedImmersion (i ≫ j) := by
    change IsClosedImmersion
      ((RootsOfUnityScheme.inclusion R n ≫ e.hom ≫ E.inclusion).left)
    rw [← torusRootsOfUnitySubgroup_curveMap]
    infer_instance
  have hpb : IsPullback i (𝟙 _) j (i ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  change (i ≫ j).ker.comap j = i.ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rw [← Scheme.Hom.ker_comp_of_isIso hpb.isoPullback.hom,
    hpb.isoPullback_hom_fst]

/-- The full subgroup ideal is relative Cartier even when the ambient curve is singular. -/
theorem torusRootsOfUnitySubgroup_relativeCartier :
    FCurve.RelativeEffectiveCartier E.curve.hom (H).ideal := by
  refine ⟨?_, (H).ideal_degree.2.1⟩
  let j := e.hom.left ≫ E.inclusion.left
  let _ : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  let _ : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (e.hom.left ≫ E.inclusion.left))
  apply FCurve.effectiveCartier_of_comap_of_support_subset (H).ideal j
  · rw [Scheme.IdealSheafData.range_subschemeι, FiniteSubgroup.ideal,
      Scheme.Hom.support_ker, (H).curveMap.left.isClosedEmbedding.isClosed_range.closure_eq]
    rintro x ⟨y, rfl⟩
    exact ⟨(RootsOfUnityScheme.inclusion R n).left y, rfl⟩
  · rw [torusRootsOfUnitySubgroup_ideal_on_torus]
    exact RootsOfUnityCartier.effectiveCartier R n

/-- Arbitrary boundary tests retain the whole-curve relative Cartier divisor. -/
theorem torusRootsOfUnitySubgroup_baseChange_relativeCartier {T : Scheme}
    (g : T ⟶ Spec (.of R)) :
    FCurve.RelativeEffectiveCartier (E.baseChange g).curve.hom ((H).baseChange g).ideal := by
  let _ : IsProper E.curve.hom := E.family.family.1
  rw [FiniteSubgroup.baseChange_ideal]
  exact FCurve.relativeCartierBaseChange E.curve.hom g (H).ideal
    (E.torusRootsOfUnitySubgroup_relativeCartier e n)

end FLT.Mazur.GeneralizedEllipticCurve
