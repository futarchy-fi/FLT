/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalLaurent
public import FLT.Mazur.WeierstrassSmoothZeroSection
public import FLT.Mazur.MultiplicativeGroupScheme

/-!
# The actual multiplicative chart of the split nodal cubic

The Laurent algebra equivalence identifies the original infinity chart with
the multiplicative group over the coefficient ring. It is a smooth open in
the original cubic, with its original structure map and zero section.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (a : Rˣ)

/-- The multiplicative group is the actual infinity chart of the split nodal equation. -/
def splitNodalTorusIso : Spec (.of R[T;T⁻¹]) ≅ chartScheme (splitNodalEquation a) 1 :=
  Scheme.Spec.mapIso (splitNodalChartLaurentEquiv a).toRingEquiv.toCommRingCatIso.op

/-- The torus comparison preserves the original coefficient morphism. -/
@[reassoc] theorem splitNodalTorusIso_structure :
    (splitNodalTorusIso a).hom ≫ chartStructure (splitNodalEquation a) 1 =
      (MultiplicativeGroupScheme.gm R).hom :=
  specAlgHom_structure (splitNodalChartToLaurent a)

/-- The nodal infinity chart and multiplicative group agree as schemes over the base. -/
def splitNodalTorusOverIso : MultiplicativeGroupScheme.gm R ≅
    Over.mk (chartStructure (splitNodalEquation a) 1) :=
  Over.isoMk (splitNodalTorusIso a) (splitNodalTorusIso_structure a)

/-- The original nodal infinity algebra is smooth without any field hypothesis. -/
instance splitNodalChart_smooth : Algebra.Smooth R (Coordinate (splitNodalEquation a) 1) := by
  let _ := MultiplicativeGroupScheme.smooth_laurent R
  exact Algebra.Smooth.of_equiv (splitNodalChartLaurentEquiv a).symm

/-- The original infinity chart structure map is smooth over the coefficient spectrum. -/
instance splitNodalChartStructure_smooth : Smooth (chartStructure (splitNodalEquation a) 1) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- The multiplicative group's actual open immersion into the original nodal cubic. -/
def splitNodalTorusToCurve : Spec (.of R[T;T⁻¹]) ⟶ integralCurve (splitNodalEquation a) :=
  (splitNodalTorusIso a).hom ≫ integralCurveChart (splitNodalEquation a) 1

/-- The torus comparison is an open immersion in the original glued cubic. -/
instance splitNodalTorusToCurve_isOpenImmersion : IsOpenImmersion (splitNodalTorusToCurve a) := by
  unfold splitNodalTorusToCurve
  infer_instance

/-- The entire normalized infinity chart lies in the actual relative smooth locus. -/
theorem splitNodalChart_range_smooth :
    Set.range (integralCurveChart (splitNodalEquation a) 1) ⊆
      integralSmoothOpen (splitNodalEquation a) := by
  rintro _ ⟨x, rfl⟩
  have h := integralCurveChart_preimage_smooth (splitNodalEquation a) 1
  rw [Scheme.Hom.smoothLocus_eq_top] at h
  exact h.ge (Set.mem_univ x)

/-- The torus inclusion canonically factors through the actual smooth locus. -/
def splitNodalTorusToSmooth : Spec (.of R[T;T⁻¹]) ⟶
    (integralSmoothOpen (splitNodalEquation a)).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen (splitNodalEquation a)).ι
    (splitNodalTorusToCurve a) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact splitNodalChart_range_smooth a ⟨(splitNodalTorusIso a).hom x, rfl⟩)

/-- The smooth-locus comparison retains the original nodal torus inclusion. -/
@[reassoc (attr := simp)] theorem splitNodalTorusToSmooth_inclusion :
    splitNodalTorusToSmooth a ≫ (integralSmoothOpen (splitNodalEquation a)).ι =
      splitNodalTorusToCurve a := IsOpenImmersion.lift_fac _ _ _

/-- The multiplicative chart is open in the actual smooth locus. -/
instance splitNodalTorusToSmooth_isOpenImmersion : IsOpenImmersion (splitNodalTorusToSmooth a) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

end FLT.Mazur.WeierstrassIntegralChart
