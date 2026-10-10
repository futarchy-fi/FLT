/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureHopf

/-!
# The recovered Hopf operations are the actual geometric operations

The counit is the original zero section, the antipode is descended geometric
negation, and comultiplication is the reflected affine multiplication.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Functor Monoidal MonoidalCategory

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]
  [IsDedekindDomain A] (hΔ : IsUnit W.Δ)

/-- The Hopf counit is precisely the original zero section under affine comparison. -/
theorem globalClosureHopf_counit_spec :
    letI := globalClosureHopfAlgebra A W H hΔ
    Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom A (GlobalClosure A W H)).toRingHom) =
      integralSection A W H 0 ≫ (gluedClosure A W H 1 2).isoSpec.hom := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  let _ : (algSpec (.of A)).Monoidal := braidedAlgSpec.toMonoidal
  change ((algSpec (.of A)).map (closureCoordinateGrpObj A W H hΔ).one).left = _
  have he := congrArg Over.Hom.left
    ((algSpec.fullyFaithful (R := .of A)).map_preimage
      (OplaxMonoidal.η (algSpec (.of A)) ≫ (closureAffineGrpObj A W H hΔ).one))
  change _ = (𝟙 (Spec (.of A))) ≫
    (integralSection A W H 0 ≫ (gluedClosure A W H 1 2).isoSpec.hom) at he
  rw [Category.id_comp] at he
  exact he

/-- The Hopf antipode is precisely the actual descended negation in affine coordinates. -/
theorem globalClosureHopf_antipode_spec :
    letI := globalClosureHopfAlgebra A W H hΔ
    Spec.map (CommRingCat.ofHom (HopfAlgebra.antipodeAlgHom A (GlobalClosure A W H)).toRingHom) =
      (gluedClosure A W H 1 2).isoSpec.inv ≫ closureNegation A W H ≫
        (gluedClosure A W H 1 2).isoSpec.hom := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  let _ : (algSpec (.of A)).Monoidal := braidedAlgSpec.toMonoidal
  exact congrArg Over.Hom.left
    ((algSpec.fullyFaithful (R := .of A)).map_preimage
      (closureAffineGrpObj A W H hΔ).inv)

/-- Comultiplication is the actual affine multiplication, with the tensor-product comparison. -/
theorem globalClosureHopf_comul_spec :
    letI := globalClosureHopfAlgebra A W H hΔ
    Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom A (GlobalClosure A W H)).toRingHom) =
      (pullbackSpecIso A (GlobalClosure A W H) (GlobalClosure A W H)).inv ≫
        (closureAffineGrpObj A W H hΔ).mul.left := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  let _ : (algSpec (.of A)).Monoidal := braidedAlgSpec.toMonoidal
  exact congrArg Over.Hom.left
    ((algSpec.fullyFaithful (R := .of A)).map_preimage
      (OplaxMonoidal.δ (algSpec (.of A)) _ _ ≫ (closureAffineGrpObj A W H hΔ).mul))

end FLT.Mazur.EllipticSubgroupChart
