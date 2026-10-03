/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ConnectingCupCompatibility

/-!
# Scalar coefficient maps in the integral complex

A scalar-linear equivariant coefficient map is also Z-linear. Its action
on the integral complex commutes with cups by characters of the original scalar ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G M P Q : Type} [CommRing k] [Group G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [AddCommGroup Q] [Module k Q] [DistribMulAction G Q] [SMulCommClass G k Q]

/-- An equivariant scalar-linear coefficient map restricts to integral coefficients. -/
def integralCoefficientRestriction
    (φ : Rep.of (Representation.ofDistribMulAction k G M) ⟶
      Rep.of (Representation.ofDistribMulAction k G P)) :
    Rep.of (Representation.ofDistribMulAction ℤ G M) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ G P) :=
  Rep.ofHom ⟨φ.hom.toLinearMap.toAddMonoidHom.toIntLinearMap, fun g => by
    ext x
    exact Rep.hom_comm_apply φ g x⟩

/-- Restricting scalars preserves the zero composite of an actual coefficient sequence. -/
theorem integralCoefficientRestriction_comp_zero
    (φ : Rep.of (Representation.ofDistribMulAction k G M) ⟶
      Rep.of (Representation.ofDistribMulAction k G P))
    (ψ : Rep.of (Representation.ofDistribMulAction k G P) ⟶
      Rep.of (Representation.ofDistribMulAction k G Q)) (h : φ ≫ ψ = 0) :
    integralCoefficientRestriction φ ≫ integralCoefficientRestriction ψ = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun t => t.hom x) h

variable [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]

/-- Integral coefficient maps still commute with cups by scalar-valued characters. -/
theorem integralCoefficientRestriction_cupOne
    (φ : Rep.of (Representation.ofDistribMulAction k G M) ⟶
      Rep.of (Representation.ofDistribMulAction k G P))
    (c : (continuousCochains ℤ G M).X 1) (d : ContinuousScalarCharacter G k) :
    ((continuousCoefficientMap (integralCoefficientRestriction φ)).f 2).hom
        (integralCupOne c d) =
      integralCupOne
        (((continuousCoefficientMap (integralCoefficientRestriction φ)).f 1).hom c) d := by
  apply Subtype.ext
  funext x
  exact φ.hom.toLinearMap.map_smul (d.val (x 1)) (c.val (fun _ => x 0))

/-- The degree-two cup has the same coefficient compatibility in the integral complex. -/
theorem integralCoefficientRestriction_cupTwo
    (φ : Rep.of (Representation.ofDistribMulAction k G M) ⟶
      Rep.of (Representation.ofDistribMulAction k G P))
    (c : (continuousCochains ℤ G M).X 2) (d : ContinuousScalarCharacter G k) :
    ((continuousCoefficientMap (integralCoefficientRestriction φ)).f 3).hom
        (integralCupTwo c d) =
      integralCupTwo
        (((continuousCoefficientMap (integralCoefficientRestriction φ)).f 2).hom c) d := by
  apply Subtype.ext
  funext x
  exact φ.hom.toLinearMap.map_smul (d.val (x 2)) (c.val ![x 0, x 1])

end LocalClassFieldTheory
