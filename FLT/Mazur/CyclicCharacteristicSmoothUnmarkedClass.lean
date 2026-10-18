/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicLocallyNormalizedModuli

/-!
# The canonical unmarked sheaf class of an original smooth object

Every original smooth ample cyclic family defines a class in the constructed
fppf quotient. It is independent of full compatible presentation and commutes
with arbitrary base change. When an original parameter is available, its
value is exactly the original parameter image, without a new choice of generator.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- A locally normalized original class agrees with every global quotient representative. -/
theorem locallyNormalizedModuliMap_eq_class {S : Scheme}
    (z : (locallyNormalizedModuli n).toFunctor.obj (Opposite.op S))
    (q : unmarkedParameterClasses n S) (hq : unmarkedParameterClassMap n S q = z.val) :
    (locallyNormalizedModuliMap n).app (Opposite.op S) z =
      (unmarkedClassToSheaf n).app (Opposite.op S) q := by
  have he := congrArg (fun a ↦ a.app (Opposite.op S) q) (locallyNormalizedModuliMap_class n)
  have hz : (Subfunctor.homOfLe
      ((normalizedModuliImage n).le_sheafify Scheme.fppfTopology)).app (Opposite.op S)
      ((Subfunctor.toRange (unmarkedParameterModuliMap n)).app (Opposite.op S) q) = z :=
    Subtype.ext hq
  change (locallyNormalizedModuliMap n).app (Opposite.op S) _ = _ at he
  exact (congrArg ((locallyNormalizedModuliMap n).app (Opposite.op S)) hz).symm.trans he

variable {S : Scheme} {E : GeneralizedEllipticCurve S} [Smooth E.curve.hom]
  (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)

/-- The canonical unmarked sheaf class of the original smooth ample cyclic family. -/
def smoothUnmarkedClass : (unmarkedParameterSheaf n).obj.obj (Opposite.op S) :=
  (locallyNormalizedModuliMap n).app (Opposite.op S)
    ⟨Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩, smooth_mem_locallyNormalizedModuli n H hc ha⟩

/-- Any actual global normalized parameter gives this same canonical original class. -/
theorem smoothUnmarkedClass_parameter (b : Bool) (q : S ⟶ normalizedLocus n b)
    (hq : (normalizedModuliMap n b).app (Opposite.op S) (ULift.up q) =
      Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) :
    smoothUnmarkedClass n H hc ha =
      (unmarkedParameterSheafMap n).app (Opposite.op S) ⟨b, ULift.up q⟩ :=
  locallyNormalizedModuliMap_eq_class n _ (Quotient.mk _ ⟨b, ULift.up q⟩) hq

/-- Full compatible isomorphisms preserve the canonical original unmarked sheaf class. -/
theorem smoothUnmarkedClass_compatible {F : GeneralizedEllipticCurve S}
    [Smooth F.curve.hom] (J : F.FiniteSubgroup n) (jc : J.IsCyclic) (ja : J.IsAmple)
    (a : CompatibleIso H J) :
    smoothUnmarkedClass n H hc ha = smoothUnmarkedClass n J jc ja := by
  apply congrArg ((locallyNormalizedModuliMap n).app (Opposite.op S))
  exact Subtype.ext (Quotient.sound ⟨a⟩)

/-- The canonical original unmarked class commutes with every base change. -/
theorem smoothUnmarkedClass_pullback {T : Scheme} (g : T ⟶ S)
    [Smooth (E.baseChange g).curve.hom] :
    (unmarkedParameterSheaf n).obj.map g.op (smoothUnmarkedClass n H hc ha) =
      smoothUnmarkedClass n (H.baseChange g) (hc.baseChange H g) (ha.baseChange g) := by
  exact (NatTrans.naturality_apply (locallyNormalizedModuliMap n) g.op
    ⟨Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩, smooth_mem_locallyNormalizedModuli n H hc ha⟩).symm

end FLT.Mazur.CyclicCharacteristicAtlas
