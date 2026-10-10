/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupAmbientPoints
public import FLT.Mazur.EllipticSubgroupGlobalEvaluation

/-!
# Actual generic subgroup points are schematically dense in their closure

The generic point of the valuation ring is dense. Each integral subgroup
section is consequently contained in the closure of its generic point, and
the covering sections prove density of the full generic family.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)

/-- The fraction-field point is dense in the original valuation-ring spectrum. -/
theorem valuationGeneric_denseRange :
    DenseRange (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  change RingHom.ker (algebraMap A K) ≤ _
  rw [(RingHom.injective_iff_ker_eq_bot (algebraMap A K)).mp Subtype.coe_injective]
  exact bot_le

/-- The actual generic subgroup points as one morphism into the constructed closure. -/
def closureGenericPointsMap : (∐ fun _ : H => Spec (.of K)) ⟶ gluedClosure A W H 1 2 :=
  Sigma.desc (closureGenericPoint A W H)

/-- Each summand is the previously constructed generic section. -/
@[reassoc] theorem closureGenericPointsMap_point (P : H) :
    Sigma.ι (fun _ : H => Spec (.of K)) P ≫ closureGenericPointsMap A W H =
      closureGenericPoint A W H P := Sigma.ι_comp_desc _ _

variable [Finite H]

/-- No closed subset smaller than the closure contains all prescribed generic points. -/
theorem closureGenericPointsMap_denseRange : DenseRange (closureGenericPointsMap A W H) := by
  intro x
  obtain ⟨P, y, rfl⟩ := integralSections_cover A W H x
  refine (valuationGeneric_denseRange A).induction_on y ?_ ?_
  · exact isClosed_closure.preimage (integralSection A W H P).continuous
  · intro z
    apply subset_closure
    refine ⟨Sigma.ι (fun _ : H => Spec (.of K)) P z, ?_⟩
    change (Sigma.ι (fun _ : H => Spec (.of K)) P ≫ closureGenericPointsMap A W H) z = _
    rw [closureGenericPointsMap_point]
    rfl

/-- The generic family is dominant as a morphism of schemes. -/
instance closureGenericPointsMap_isDominant : IsDominant (closureGenericPointsMap A W H) :=
  ⟨closureGenericPointsMap_denseRange A W H⟩

/-- The finite generic family is quasi-compact. -/
instance closureGenericPointsMap_quasiCompact : QuasiCompact (closureGenericPointsMap A W H) := by
  have : IsAffine (∐ fun _ : H => Spec (.of K)) := inferInstance
  infer_instance

/-- The actual generic family detects the scheme structure, including all integral equations. -/
instance closureGenericPointsMap_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (closureGenericPointsMap A W H) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

/-- The ambient closure ideal equals the kernel of the actual generic subgroup family. -/
theorem closureToCurve_ker_eq_generic : (closureToCurve A W H 1 2).ker =
    (closureGenericPointsMap A W H ≫ closureToCurve A W H 1 2).ker := by
  rw [Scheme.Hom.ker_comp, (closureGenericPointsMap A W H).ker_eq_bot,
    Scheme.IdealSheafData.map_bot]

end FLT.Mazur.EllipticSubgroupChart
