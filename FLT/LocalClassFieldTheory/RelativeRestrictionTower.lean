/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AbsoluteRestriction
public import FLT.LocalClassFieldTheory.GaloisInflationH2

/-!
# Restriction of finite relative classes in a tower

For K ⊆ E ⊆ F ⊆ C, restrict from Gal(F/K) to Gal(F/E), without
changing coefficients. Inflation to C commutes with this actual restriction.
The intermediate extension E/K need not be Galois.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable (K C : Type) [Field K] [Field C] [Algebra K C] [IsGalois K C]
  (E : IntermediateField K C) (F : IntermediateField E C)
  [IsGalois K (F.restrictScalars K)] [IsGalois E F]
  [FiniteDimensional K (F.restrictScalars K)]

attribute [local instance] fieldUnitAction

/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeRestrictionGalois : IsGalois K F :=
  inferInstanceAs (IsGalois K (F.restrictScalars K))
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeRestrictionFinite : FiniteDimensional K F :=
  inferInstanceAs (FiniteDimensional K (F.restrictScalars K))
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeRestrictionFiniteOverBase : FiniteDimensional E F :=
  FiniteDimensional.right K E F

/-- The coefficient identity for finite relative restriction. -/
def relativeRestrictionCoefficients :
    Rep.res (AlgEquiv.restrictScalarsHom K : Gal(F/E) →* Gal(F/K))
      (Rep.of (Representation.ofDistribMulAction ℤ Gal(F/K) (Additive Fˣ))) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ Gal(F/E) (Additive Fˣ)) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

variable [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)]

/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeRestrictionUnitTopology :
    TopologicalSpace (Additive (F.restrictScalars K)ˣ) :=
  inferInstanceAs (TopologicalSpace (Additive Fˣ))
/-- The canonical tower instance with the intermediate-field presentation made explicit. -/
local instance relativeRestrictionUnitDiscrete :
    DiscreteTopology (Additive (F.restrictScalars K)ˣ) :=
  inferInstanceAs (DiscreteTopology (Additive Fˣ))

/-- Restriction on the actual continuous finite relative cochain complex. -/
def relativeRestrictionComplex : continuousCochains ℤ Gal(F/K) (Additive Fˣ) ⟶
    continuousCochains ℤ Gal(F/E) (Additive Fˣ) :=
  continuousRestriction (AlgEquiv.restrictScalarsHom K)
    continuous_of_discreteTopology (relativeRestrictionCoefficients K C E F)

/-- Restriction on finite relative cohomology, retaining the top field's units. -/
def relativeRestriction (n : ℕ) : continuousCohomology ℤ Gal(F/K) (Additive Fˣ) n ⟶
    continuousCohomology ℤ Gal(F/E) (Additive Fˣ) n :=
  homologyMap (relativeRestrictionComplex K C E F) n

omit [IsGalois K C] [FiniteDimensional K (F.restrictScalars K)]
  [TopologicalSpace (Additive Fˣ)] [DiscreteTopology (Additive Fˣ)]
  [TopologicalSpace (Additive Cˣ)] [DiscreteTopology (Additive Cˣ)] in
/-- Restricting a top-field automorphism commutes with forgetting its intermediate scalars. -/
theorem relativeRestriction_group_square (g : Gal(C/E)) :
    (AlgEquiv.restrictNormalHom F g).restrictScalars K =
      AlgEquiv.restrictNormalHom (F.restrictScalars K) (g.restrictScalars K) := by
  ext x
  exact (AlgEquiv.restrictNormal_apply F g x).trans
    (AlgEquiv.restrictNormal_apply (F.restrictScalars K) (g.restrictScalars K) x).symm

/-- The relative/absolute restriction square commutes before taking cohomology. -/
theorem relativeRestriction_inflation_complex :
    relativeRestrictionComplex K C E F ≫
      continuousRestriction (AlgEquiv.restrictNormalHom F)
        (InfiniteGalois.restrictNormalHom_continuous F)
        (galoisInflationCoefficients E C F) =
    continuousRestriction (AlgEquiv.restrictNormalHom (F.restrictScalars K))
        (InfiniteGalois.restrictNormalHom_continuous (F.restrictScalars K))
        (galoisInflationCoefficients K C (F.restrictScalars K)) ≫
      absoluteRestrictionComplex K C E := by
  ext n c : 3
  apply Subtype.ext
  funext g
  change Additive.ofMul (Units.map F.val.toMonoidHom
    (c.val (fun i => (AlgEquiv.restrictNormalHom F (g i)).restrictScalars K)).toMul) =
      Additive.ofMul (Units.map F.val.toMonoidHom
        (c.val (fun i => AlgEquiv.restrictNormalHom (F.restrictScalars K)
          ((g i).restrictScalars K))).toMul)
  congr 4

/-- Actual finite relative restriction commutes with inflation to the common closure. -/
theorem relativeRestriction_inflation (n : ℕ) :
    relativeRestriction K C E F n ≫ galoisMultiplicativeInflation E C F n =
      galoisMultiplicativeInflation K C (F.restrictScalars K) n ≫
        absoluteRestriction K C E n := by
  unfold relativeRestriction galoisMultiplicativeInflation absoluteRestriction
  rw [← homologyMap_comp, ← homologyMap_comp, relativeRestriction_inflation_complex]

end LocalClassFieldTheory
