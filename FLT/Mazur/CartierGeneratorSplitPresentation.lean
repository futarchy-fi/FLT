/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorCyclicMap
public import FLT.Mazur.ConstantCyclicRelativeClosed

/-!
# Reconstructing a subgroup from a universally distinct Cartier generator

The Cartier orbit identity identifies the closed image of the constant cyclic
group with the original subgroup. This constructs a group-scheme isomorphism,
retaining every power section and its inclusion in the original whole curve.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open UniversallyDistinctSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) {P : 𝟙_ (Over S) ⟶ H.carrier}
  (hP : H.IsCartierGenerator P)
  (hd : UniversallyDistinct (fun i : ZMod n ↦
    H.generatorPowers P hP.1 (Multiplicative.ofAdd i)))

include hd
/-- Universal distinctness embeds the constant group into the original subgroup. -/
theorem generatorCyclicMap_closed : IsClosedImmersion (H.generatorCyclicMap P hP.1).left :=
  ConstantCyclicRelativeClosed.toScheme_closed _ hd

/-- The closed image retains the full scheme-theoretic subgroup ideal. -/
theorem generatorCyclicMap_curve_kernel :
    ((H.generatorCyclicMap P hP.1) ≫ H.curveMap).left.ker = H.ideal := by
  have : IsProper E.curve.hom := E.family.family.1
  have hdc : UniversallyDistinct (fun i : ZMod n ↦
      ConstantCyclicGroup.component S n i ≫
        ((H.generatorCyclicMap P hP.1) ≫ H.curveMap)) := by
    intro V g hV i j hij
    apply hd V g hV
    have : Mono H.curveMap := Over.mono_of_mono_left H.curveMap
    apply (cancel_mono H.curveMap).mp
    simpa only [generatorCyclicMap, Category.assoc,
      ConstantCyclicSectionMap.component_toScheme_assoc] using hij
  rw [ConstantCyclicRelativeClosed.kernel_eq_component_product _ hdc]
  apply Eq.trans _ hP.2.2.symm
  rw [← Equiv.prod_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.prod_congr rfl
  intro i _
  change (ConstantCyclicGroup.component S n (ZMod.finEquiv n i) ≫
    (H.generatorCyclicMap P hP.1 ≫ H.curveMap)).left.ker = _
  rw [ConstantCyclicGenerator.component_pow, ← Category.assoc, MonObj.pow_comp]
  have he : ConstantCyclicGroup.component S n 1 ≫ H.generatorCyclicMap P hP.1 = P := by
    simpa using H.generatorCyclicMap_component P hP.1 1
  rw [he]


/-- The actual cyclic morphism is an isomorphism, proved from the Cartier ideal identity. -/
theorem generatorCyclicMap_isIso : IsIso (H.generatorCyclicMap P hP.1) := by
  have := H.generatorCyclicMap_closed hP hd
  have : IsClosedImmersion
      ((H.generatorCyclicMap P hP.1).left ≫ H.curveMap.left) := inferInstance
  have : IsIso (H.generatorCyclicMap P hP.1).left :=
    IsClosedImmersion.isIso_of_ker_eq
      ((H.generatorCyclicMap P hP.1).left ≫ H.curveMap.left) H.curveMap.left
      (H.generatorCyclicMap P hP.1).left rfl (H.generatorCyclicMap_curve_kernel hP hd)
  let _ : IsIso ((Over.forget S).map (H.generatorCyclicMap P hP.1)) :=
    inferInstanceAs (IsIso (H.generatorCyclicMap P hP.1).left)
  exact isIso_of_reflects_iso (H.generatorCyclicMap P hP.1) (Over.forget S)

/-- The constant cyclic presentation of the original subgroup, retaining its generator. -/
def generatorSplitIso : ConstantCyclicGroup.model S n ≅ H.carrier := by
  let _ := H.generatorCyclicMap_isIso hP hd
  exact asIso (H.generatorCyclicMap P hP.1)

/-- The reconstructed subgroup isomorphism is a group isomorphism. -/
instance generatorSplitIso_isMonHom : IsMonHom (H.generatorSplitIso hP hd).hom :=
  inferInstanceAs (IsMonHom (H.generatorCyclicMap P hP.1))

/-- Every marked orbit section survives the constructed presentation. -/
@[reassoc] theorem generatorSplitIso_component (k : ℕ) :
    ConstantCyclicGroup.component S n (k : ZMod n) ≫ (H.generatorSplitIso hP hd).hom =
      P ^ k := H.generatorCyclicMap_component P hP.1 k

/-- A universally distinct Cartier generator forces the actual subgroup to be etale. -/
theorem etale_of_distinct_cartierGenerator : Etale H.carrier.hom := by
  have : IsIso (H.generatorSplitIso hP hd).inv.left :=
    inferInstanceAs (IsIso ((Over.forget S).mapIso (H.generatorSplitIso hP hd)).inv)
  have := ConstantCyclicRelativeGeometry.etale S n
  rw [← (H.generatorSplitIso hP hd).inv.w]
  infer_instance

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
