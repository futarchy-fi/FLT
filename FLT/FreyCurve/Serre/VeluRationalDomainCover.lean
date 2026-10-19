/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelPointRegularity
public import FLT.Mazur.AlgClosedOpenCover

/-!
# The original Vélu rational domain is the entire source scheme

The classical point comparison covers every base-field section. Finite-type
Jacobson geometry then rules out any nonempty closed complement.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

omit [CharZero K] [IsAlgClosed K] [DecidableEq K] in
/-- Every actual section of the source is an original point of its affine group. -/
theorem exists_affineSmoothPoint_of_section (p : Spec (.of K) ⟶ integralCurve E)
    (hp : p ≫ integralCurveStructure E = 𝟙 _) :
    ∃ P : E.toAffine.Point, affineSmoothPoint E P ≫ (integralSmoothOpen E).ι = p := by
  classical
  let q : integralCurveFieldPoint (K := K) E := Over.homMk p (by
    change p ≫ integralCurveStructure E = Spec.map (𝟙 (CommRingCat.of K))
    rw [Spec.map_id]
    exact hp)
  obtain ⟨P, hP⟩ := projectiveToIntegral_surjective E IsElliptic.isUnit q
  let A := Projective.Point.toAffineAddEquiv (E.map (algebraMap K K)).toProjective
  refine ⟨A P, ?_⟩
  have he : Projective.Point.fromAffine (A P) = P := A.symm_apply_apply P
  rw [affineSmoothPoint, he, projectiveToSmooth_inclusion]
  exact congrArg Over.Hom.left hP

/-- All actual base-field sections land in the domain of the original rational map. -/
theorem veluSection_range_subset_rationalDomain (p : Spec (.of K) ⟶ integralCurve E)
    (hp : p ≫ integralCurveStructure E = 𝟙 _) :
    Set.range p ⊆ (veluSchemeRationalMap E G hodd).domain := by
  obtain ⟨P, rfl⟩ := exists_affineSmoothPoint_of_section E p hp
  rintro _ ⟨z, rfl⟩
  exact veluOriginalPoint_mem_rationalDomain E G hodd P z

/-- The original rational map is defined at every scheme point, including nonclosed points. -/
theorem veluSchemeRationalMap_domain_eq_top :
    (veluSchemeRationalMap E G hodd).domain = ⊤ :=
  FLT.Mazur.AlgClosedOpenCover.eq_top_of_sections (integralCurveStructure E) _
    (veluSection_range_subset_rationalDomain E G hodd)

end WeierstrassCurve.Velu
