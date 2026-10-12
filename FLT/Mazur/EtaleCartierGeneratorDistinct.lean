/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCartierGeneratorGeometric
public import FLT.Mazur.UniversallyDistinctSections
public import FLT.Mazur.GeometricPointCoverCriterion

/-!
# Etale Cartier generators are universally distinct

Any coincidence on a nonempty test scheme survives at a geometric point of
that test. The actual pulled-back subgroup has degree n and its generator
has n distinct geometric powers, ruling out the original coincidence.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) [Etale H.carrier.hom]
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

/-- An etale Cartier generator is faithful on every nonempty scheme test. -/
theorem IsCartierGenerator.universallyDistinct :
    UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦
      H.generatorPowers P hP.1 (Multiplicative.ofAdd i)) := by
  intro V g hV i j hij
  let v : V.left := Classical.choice hV
  let K := AlgebraicClosure (V.left.residueField v)
  let a : Spec (.of K) ⟶ V.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (V.left.residueField v) K)) ≫
      V.left.fromSpecResidueField v
  let f : Spec (.of K) ⟶ S := a ≫ V.hom
  let _ : Etale (H.baseChange f).carrier.hom := by
    change Etale (pullback.snd H.carrier.hom f)
    infer_instance
  have hh : H.pullGenerator f P ^ i.val = H.pullGenerator f P ^ j.val := by
    change GroupSectionBaseChange.pullSection f P ^ i.val =
      GroupSectionBaseChange.pullSection f P ^ j.val
    rw [← GroupSectionBaseChange.section_pow, ← GroupSectionBaseChange.section_pow]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [GroupSectionBaseChange.section_fst, GroupSectionBaseChange.section_fst]
      have hg : g.left = V.hom := by simpa using g.w
      have he := congrArg (fun s : V ⟶ H.carrier ↦ a ≫ s.left) hij
      change a ≫ g.left ≫ (P ^ i.val).left = a ≫ g.left ≫ (P ^ j.val).left at he
      simpa only [f, hg, Category.assoc] using he
    · exact (Over.w _).trans (Over.w _).symm
  have he := (hP.baseChange H f).geometric_powers_injective (H.baseChange f)
    (a₁ := ⟨i.val, ZMod.val_lt i⟩) (a₂ := ⟨j.val, ZMod.val_lt j⟩) hh
  exact ZMod.val_injective n (congrArg Fin.val he)

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
