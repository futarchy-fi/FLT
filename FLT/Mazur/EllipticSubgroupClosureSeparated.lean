/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupOverlapGraph
public import FLT.Mazur.EllipticSubgroupClosureProperties
public import FLT.Mazur.OneGonSeparated

/-!
# Separatedness of the actual glued subgroup closure

The specified overlap is the actual intersection in the gluing. Its closed graph
and the affine chart diagonals prove that the structural morphism is separated.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- The designated principal overlap is the actual intersection of the closure charts. -/
theorem closureChart_isPullback : IsPullback
    (closureToLeft A W H j k) (closureToRight A W H j k)
      (closureLeft A W H j k) (closureRight A W H j k) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (closure_overlap_condition A W H j k).symm
  apply TopologicalSpace.Opens.ext
  ext x
  change closureRight A W H j k x ∈ Set.range (closureLeft A W H j k) ↔
    x ∈ Set.range (closureToRight A W H j k)
  constructor
  · rintro ⟨y, hy⟩
    change colimit.ι (span (closureToLeft A W H j k) (closureToRight A W H j k))
      WalkingSpan.left y = colimit.ι
        (span (closureToLeft A W H j k) (closureToRight A W H j k)) WalkingSpan.right x at hy
    obtain ⟨a, fi, fj, z, _, hz⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff _).mp hy
    cases fi <;> cases fj
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨closureToLeft A W H j k z,
      congrArg (fun f => f z) (closure_overlap_condition A W H j k)⟩

/-- The mixed intersection map is a closed immersion into the product over the base. -/
theorem closure_mixed_isClosedImmersion : IsClosedImmersion
    (pullback.mapDesc (closureLeft A W H j k) (closureRight A W H j k)
      (closureToBase A W H j k)) := by
  let e := pullback.congrHom (closureLeft_toBase A W H j k) (closureRight_toBase A W H j k)
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ e.hom,
    ← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      (closureChart_isPullback A W H j k).isoPullback.hom]
  have he : (closureChart_isPullback A W H j k).isoPullback.hom ≫
      pullback.mapDesc (closureLeft A W H j k) (closureRight A W H j k)
        (closureToBase A W H j k) ≫ e.hom = closureOverlapGraph A W H j k := by
    apply pullback.hom_ext <;> simp [e, pullback.mapDesc, closureOverlapGraph]
  rw [he]
  infer_instance

/-- Gluing along the actual homogeneous transition gives a separated structural map. -/
instance closureToBase_isSeparated : IsSeparated (closureToBase A W H j k) := by
  apply SeparatedOpenCover.of_pairwise _ (closureOpenCover A W H j k)
  intro i l
  cases i <;> cases l
  · have : IsSeparated (closureLeft A W H j k ≫ closureToBase A W H j k) := by
      rw [closureLeft_toBase]
      exact inferInstanceAs (IsSeparated (Spec.map _))
    exact OneGonSeparated.same_closed (closureLeft A W H j k) (closureToBase A W H j k)
  · exact closure_mixed_isClosedImmersion A W H j k
  · have := closure_mixed_isClosedImmersion A W H j k
    exact OneGonSeparated.reversed_closed (closureLeft A W H j k)
      (closureRight A W H j k) (closureToBase A W H j k)
  · have : IsSeparated (closureRight A W H j k ≫ closureToBase A W H j k) := by
      rw [closureRight_toBase]
      exact inferInstanceAs (IsSeparated (Spec.map _))
    exact OneGonSeparated.same_closed (closureRight A W H j k) (closureToBase A W H j k)

end FLT.Mazur.EllipticSubgroupChart
