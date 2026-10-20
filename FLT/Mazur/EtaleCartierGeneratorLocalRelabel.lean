/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleGeometricGeneratorRelabel
public import FLT.Mazur.EtaleCyclicSubgroupLocalPresentation
public import FLT.Mazur.UnramifiedGeometricSectionMatching

/-!
# Exact local relabeling of actual etale Cartier generators

The geometric full-level unit comparison extends to a single affine
neighborhood matching every original generator power as a scheme morphism.
Subgroup etaleness is an explicit hypothesis, not inferred from geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) [Etale H.carrier.hom]
  {P Q : 𝟙_ (Over S) ⟶ H.carrier}

/-- Etale Cartier generators match on an affine neighborhood with one full-level relabeling. -/
theorem IsCartierGenerator.exists_local_relabel
    (hP : H.IsCartierGenerator P) (hQ : H.IsCartierGenerator Q) (x : S) :
    ∃ (r : MulAut (Multiplicative (ZMod n))) (U : S.Opens),
      IsAffineOpen U ∧ x ∈ U ∧ ∀ i,
        U.ι ≫ (P ^ (r i).toAdd.val).left = U.ι ≫ (Q ^ i.toAdd.val).left := by
  apply UnramifiedGeometricSectionMatching.exists_affine_relabel H.carrier.hom
    (fun i : Multiplicative (ZMod n) => (P ^ i.toAdd.val).left)
    (fun i : Multiplicative (ZMod n) => (Q ^ i.toAdd.val).left)
    (fun _ => Over.w _) (fun _ => Over.w _)
    (fun (r : MulAut (Multiplicative (ZMod n))) i => r i) ?_ x
  intro K _ _ q
  obtain ⟨u, hu⟩ := (hP.baseChange H q).exists_unit_power (H.baseChange q)
    (hQ.baseChange H q)
  refine ⟨CyclicUnitRelabeling.labelAut u, fun i => ?_⟩
  have he : pullSection q P ^ ((CyclicUnitRelabeling.labelAut u) i).toAdd.val =
      pullSection q Q ^ i.toAdd.val := by
    change H.pullGenerator q P ^ ((CyclicUnitRelabeling.labelAut u) i).toAdd.val =
      H.pullGenerator q Q ^ i.toAdd.val
    rw [CyclicUnitRelabeling.relabeled_power _ (hP.baseChange H q).1, hu]
  rw [← section_pow, ← section_pow] at he
  have h := congrArg (fun z => z.left ≫ pullback.fst H.carrier.hom q) he
  simpa only [section_fst] using h

variable {H} {J : F.FiniteSubgroup n} [Etale J.carrier.hom]
  (a : CompatibleIso H J) {R : 𝟙_ (Over S) ⟶ J.carrier}

omit [Etale H.carrier.hom] in
/-- The same local relabeling preserves the original compatible subgroup comparison. -/
theorem CompatibleIso.exists_local_generator_relabel
    (hP : H.IsCartierGenerator P) (hR : J.IsCartierGenerator R) (x : S) :
    ∃ (r : MulAut (Multiplicative (ZMod n))) (U : S.Opens),
      IsAffineOpen U ∧ x ∈ U ∧ ∀ i,
        U.ι ≫ (P ^ (r i).toAdd.val).left ≫ a.subgroup.hom.left =
          U.ι ≫ (R ^ i.toAdd.val).left := by
  obtain ⟨r, U, hU, hx, he⟩ := (a.cartierGenerator hP).exists_local_relabel J hR x
  refine ⟨r, U, hU, hx, fun i => ?_⟩
  simpa only [← pow_comp, Over.comp_left] using he i

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
