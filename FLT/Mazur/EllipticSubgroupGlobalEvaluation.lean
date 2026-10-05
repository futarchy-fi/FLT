/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupGlobalAlgebra
public import FLT.Mazur.SchemeCoproductSections
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Global functions are detected by actual integral subgroup sections

Each chart embeds into a product of fields, so the glued closure is reduced.
The surjective section family is therefore schematically dominant. Pulling back
global functions gives an injection into the product of copies of the base ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)

/-- The chart closure has no nilpotents, since it embeds in the generic point algebra. -/
instance closure_isReduced (j : Fin 3) : _root_.IsReduced (Closure A W H j) :=
  isReduced_of_injective (AffineGenericClosure.inclusion (coordinateMap A W H j))
    (AffineGenericClosure.inclusion_injective (coordinateMap A W H j))

/-- Reducedness descends from the actual two-chart cover. -/
instance gluedClosure_isReduced (j k : Fin 3) : IsReduced (gluedClosure A W H j k) := by
  have (b : (closureOpenCover A W H j k).I₀) :
      IsReduced ((closureOpenCover A W H j k).X b) := by
    cases b <;> exact inferInstanceAs (IsReduced (Spec _))
  exact IsReduced.of_openCover _ (closureOpenCover A W H j k)

variable [Finite H]

/-- Evaluation of global coordinates on an actual integral subgroup section. -/
def globalClosureEvaluation (P : H) : GlobalClosure A W H →ₐ[A] A where
  toRingHom := ((integralSection A W H P).appTop ≫ (Scheme.ΓSpecIso (.of A)).hom).hom
  commutes' a := by
    have he : (Scheme.ΓSpecIso (.of A)).inv ≫ (closureToBase A W H 1 2).appTop ≫
        (integralSection A W H P).appTop ≫ (Scheme.ΓSpecIso (.of A)).hom = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop_assoc, integralSection_toBase]
      simp
    exact congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of A => f.hom a) he

/-- Simultaneous evaluation at every integral subgroup section. -/
def globalClosureEvaluations : GlobalClosure A W H →ₐ[A] (H → A) :=
  AlgHom.pi (globalClosureEvaluation A W H)

/-- A finite coproduct of affine base schemes makes the section-family map quasi-compact. -/
instance integralSectionsMap_quasiCompact : QuasiCompact (integralSectionsMap A W H) := by
  have : IsAffine (∐ fun _ : H => Spec (.of A)) := inferInstance
  infer_instance

/-- The covering section family is schematically dominant because the closure is reduced. -/
instance integralSectionsMap_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (integralSectionsMap A W H) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

set_option backward.isDefEq.respectTransparency false in
/-- No nonzero global function vanishes on all integral subgroup sections. -/
theorem globalClosureEvaluations_injective :
    Function.Injective (globalClosureEvaluations A W H) := by
  intro a b hab
  apply (integralSectionsMap A W H).app_injective ⊤
  apply (ConcreteCategory.bijective_of_isIso
    (SchemeCoproductSections.iso (fun _ : H => Spec (.of A))).hom).1
  apply funext
  intro P
  rw [SchemeCoproductSections.iso_apply, SchemeCoproductSections.iso_apply]
  change ((integralSectionsMap A W H).appTop ≫
      (Sigma.ι (fun _ : H => Spec (.of A)) P).appTop).hom a =
    ((integralSectionsMap A W H).appTop ≫
      (Sigma.ι (fun _ : H => Spec (.of A)) P).appTop).hom b
  rw [← Scheme.Hom.comp_appTop, integralSectionsMap, Sigma.ι_comp_desc]
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom).1
  exact congrFun hab P

end FLT.Mazur.EllipticSubgroupChart
