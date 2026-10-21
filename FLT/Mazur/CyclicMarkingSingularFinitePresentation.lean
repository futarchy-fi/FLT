/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatVanishingFinitePresentation
public import FLT.Mazur.CyclicMarkingSingularLocus
public import FLT.Mazur.GeneralizedCurveGroupRelativeDimension

/-!
# Finite equations for singular cyclic orbit closure over arbitrary bases

The orbit ideal is Cartier in the actual smooth group of every generalized
curve. Its multiplication pullback therefore has finite equations, even
though that pullback need not be Cartier. Coefficient extraction gives a
finitely presented closed multiplication locus over any original base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))

/-- The full multiplication obstruction has finite generators on every affine product chart. -/
theorem singularOrbitMultiplicationIdeal_fg (U : (E.singularOrbitProduct φ).left.affineOpens) :
    ((E.singularOrbitMultiplicationIdeal φ).ideal U).FG :=
  IdealSheafFiniteEquations.cartier_comap_ideal_fg (E.cyclicMarkingGroupIdeal φ)
    (E.cyclicMarkingGroupIdeal_cartier φ).1
    (ClosedGroupIdeal.productMap E.group (E.cyclicMarkingGroupIdeal φ)).left U

/-- The coefficient equations for orbit closure are finite on every original affine base open. -/
theorem singularOrbitCoefficientIdeal_fg (U : S.affineOpens) :
    ((E.singularOrbitCoefficientIdeal φ).ideal U).FG := by
  let g := (E.singularOrbitProduct φ).hom
  let _ := (g.app U.1).hom.toAlgebra
  let _ : Module.Finite Γ(S, U.1) Γ((E.singularOrbitProduct φ).left, g ⁻¹ᵁ U.1) :=
    g.finite_app U.1 U.2
  let _ := FCurve.finiteFlat_app_projective g U
  exact ProjectiveIdealVanishing.ideal_fg Γ(S, U.1)
    Γ((E.singularOrbitProduct φ).left, g ⁻¹ᵁ U.1)
    (FiniteFlatIdealVanishing.preimageIdeal g (E.singularOrbitMultiplicationIdeal φ) U)
    (E.singularOrbitMultiplicationIdeal_fg φ ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩)

/-- The actual closed orbit-subgroup locus is finitely presented over every original base. -/
instance singularOrbitLocusInclusion_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (E.singularOrbitLocusInclusion φ) := by
  apply FiniteFlatIdealVanishing.locusInclusion_locallyOfFinitePresentation
  intro U
  exact E.singularOrbitMultiplicationIdeal_fg φ
    ⟨(E.singularOrbitProduct φ).hom ⁻¹ᵁ U.1, U.2.preimage _⟩

end FLT.Mazur.GeneralizedEllipticCurve
