/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothCyclicMarking
public import FLT.Mazur.PolygonCompleteCartesianPointDivisor
public import FLT.Mazur.PolygonCompleteMarkingDivisor

/-!
# The original complete marking divisor is the finite cyclic carrier

The actual pulled-back product ideal cuts out the finite etale rank-n marking
scheme. Its explicit isomorphism with the constant group transports a cyclic
group structure to the divisor itself, retaining the original curve inclusion.
This does not supply a group law on the whole smooth locus.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The finite marking map has exactly the original complete product ideal. -/
theorem completeCyclicMarking_originalIdeal :
    (completeCyclicMarking K n h s p q hs).left.ker =
      (completeMarkingDivisor K n h).comap p := by
  rw [completeCyclicMarking_kernel]
  simp only [completeMarkingDivisor, FCurve.idealSheaf_comap_prod,
    completeCartesianMarking_ker K n h s p q hs]

/-- The original divisor over the chosen base, with its unchanged product ideal. -/
def completeCyclicDivisor : Over S :=
  Over.mk (((completeMarkingDivisor K n h).comap p).subschemeι ≫ q)

/-- The constant carrier is the actual closed subscheme of the original product ideal. -/
def completeCyclicDivisorSchemeIso : (ConstantCyclicGroup.model S n).left ≅
    ((completeMarkingDivisor K n h).comap p).subscheme := by
  let _ := completeCyclicMarking_closed K n h s p q hs
  have he : ((completeMarkingDivisor K n h).comap p).subschemeι.ker =
      (completeCyclicMarking K n h s p q hs).left.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, completeCyclicMarking_originalIdeal]
  let f := IsClosedImmersion.lift ((completeMarkingDivisor K n h).comap p).subschemeι
    (completeCyclicMarking K n h s p q hs).left he.le
  let _ : IsIso f := IsClosedImmersion.isIso_lift _ _ he
  exact asIso f

/-- The divisor comparison retains the original entire closed embedding. -/
@[reassoc] theorem completeCyclicDivisorSchemeIso_ι :
    (completeCyclicDivisorSchemeIso K n h s p q hs).hom ≫
      ((completeMarkingDivisor K n h).comap p).subschemeι =
        (completeCyclicMarking K n h s p q hs).left := by
  let _ := completeCyclicMarking_closed K n h s p q hs
  exact IsClosedImmersion.lift_fac _ _ _

/-- The actual divisor comparison also retains the given base projection. -/
def completeCyclicDivisorIso : ConstantCyclicGroup.model S n ≅
    completeCyclicDivisor K n h p q :=
  Over.isoMk (completeCyclicDivisorSchemeIso K n h s p q hs) (by
    change _ ≫ ((completeMarkingDivisor K n h).comap p).subschemeι ≫ q = _
    rw [completeCyclicDivisorSchemeIso_ι_assoc]
    exact (completeCyclicMarking K n h s p q hs).w)

include hs in
/-- The original complete product divisor is finite locally free of scheme-theoretic rank n. -/
theorem completeCyclicDivisor_degree :
    FCurve.FiniteLocallyFreeDegree (completeCyclicDivisor K n h p q).hom n :=
  (ConstantCyclicRelativeGeometry.degree S n).of_overIso
    (completeCyclicDivisorIso K n h s p q hs)

include hs in
/-- The actual complete marking divisor is etale over every chosen base. -/
theorem completeCyclicDivisor_etale : Etale (completeCyclicDivisor K n h p q).hom := by
  let _ := ConstantCyclicRelativeGeometry.etale S n
  rw [← Over.w (completeCyclicDivisorIso K n h s p q hs).inv]
  infer_instance

/-- The finite cyclic group laws transported to the actual product divisor. -/
abbrev completeCyclicDivisorGrpObj : GrpObj (completeCyclicDivisor K n h p q) :=
  GrpObj.ofIso (completeCyclicDivisorIso K n h s p q hs)

/-- The transported group structure on the actual divisor is commutative. -/
abbrev completeCyclicDivisorCommGrpObj : CommGrpObj (completeCyclicDivisor K n h p q) where
  __ := completeCyclicDivisorGrpObj K n h s p q hs
  mul_comm := by
    change (β_ _ _).hom ≫
      ((completeCyclicDivisorIso K n h s p q hs).inv ⊗ₘ
        (completeCyclicDivisorIso K n h s p q hs).inv) ≫
          MonObj.mul ≫ (completeCyclicDivisorIso K n h s p q hs).hom = _
    rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]
    rfl

variable [LocallyOfFinitePresentation q]

/-- The actual product divisor maps to the relative smooth open through its original markings. -/
def completeCyclicDivisorSmoothMap :
    completeCyclicDivisor K n h p q ⟶ Over.mk (q.smoothLocus.ι ≫ q) :=
  (completeCyclicDivisorIso K n h s p q hs).inv ≫ completeSmoothCyclicMarking K n h s p q hs

/-- The smooth divisor map retains exactly the original product-divisor inclusion. -/
@[reassoc] theorem completeCyclicDivisorSmoothMap_ι :
    (completeCyclicDivisorSmoothMap K n h s p q hs).left ≫ q.smoothLocus.ι =
      ((completeMarkingDivisor K n h).comap p).subschemeι := by
  apply (cancel_epi (completeCyclicDivisorSchemeIso K n h s p q hs).hom).mp
  change (completeCyclicDivisorSchemeIso K n h s p q hs).hom ≫
    (completeCyclicDivisorSchemeIso K n h s p q hs).inv ≫
      (completeSmoothCyclicMarking K n h s p q hs).left ≫ q.smoothLocus.ι = _
  rw [Iso.hom_inv_id_assoc, completeSmoothCyclicMarking_ι,
    completeCyclicDivisorSchemeIso_ι]

/-- The original product divisor is closed in the actual relative smooth open. -/
theorem completeCyclicDivisorSmoothMap_closed :
    IsClosedImmersion (completeCyclicDivisorSmoothMap K n h s p q hs).left := by
  let _ : IsClosedImmersion ((completeCyclicDivisorSmoothMap K n h s p q hs).left ≫
      q.smoothLocus.ι) := by
    rw [completeCyclicDivisorSmoothMap_ι]
    infer_instance
  exact IsClosedImmersion.of_comp _ q.smoothLocus.ι

end FLT.Mazur.PolygonInfinitesimalStages
