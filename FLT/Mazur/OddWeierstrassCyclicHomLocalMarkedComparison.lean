/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleTorsionCurveMarkingRelabel
public import FLT.Mazur.OddWeierstrassCyclicHomGeometricMarkedComparison
public import FLT.Mazur.OddWeierstrassAuxiliaryInvertibleTorsion
public import FLT.Mazur.OddWeierstrassAuxiliaryLocalRelabel

/-!
# Both original frames match on one actual affine neighborhood

At invertible level, one auxiliary automorphism and one cyclic automorphism
match the original compatible family comparison on the same affine open.
All equalities are exact scheme morphism equalities over the original base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f g : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (hf : cyclicHomMultiplicationEquation n f = 0)
  (hg : cyclicHomMultiplicationEquation n g = 0)
  (a : CompatibleIso (cyclicHomSubgroup n f hf) (cyclicHomSubgroup n g hg))

/-- Both actual source markings align on one affine neighborhood at every invertible level. -/
theorem cyclicHom_local_marking_relabel (hn : IsUnit (n : Γ(T, ⊤))) (x : T) :
    ∃ (r : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n))) (U : T.Opens),
      IsAffineOpen U ∧ x ∈ U ∧
      (∀ i, U.ι ≫ (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) (r i)).left ≫
        a.curve.hom.group.left =
          U.ι ≫ (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i).left) ∧
      (∀ i, U.ι ≫ (cyclicHomSourceMarking n f (c i)).left ≫ a.curve.hom.group.left =
        U.ι ≫ (cyclicHomSourceMarking n g i).left) := by
  let _ : IsMonHom (groupIso a.curve).hom :=
    inferInstanceAs (IsMonHom a.curve.hom.group)
  let e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g) :=
    CommGrp.mkIso' (groupIso a.curve)
  obtain ⟨r, U, _, hxU, hr⟩ := auxiliarySchemeMarking_local_relabel _ _ e x
  change ∀ i, U.ι ≫
    (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) (r i)).left ≫
      a.curve.hom.group.left =
        U.ι ≫ (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i).left at hr
  let _ : IsProper (cyclicHomSourceCurve n g).curve.hom :=
    (cyclicHomSourceCurve n g).family.family.1
  let _ : IsSeparated (cyclicHomSourceCurve n g).group.hom := by
    rw [← (cyclicHomSourceCurve n g).inclusion.w]
    infer_instance
  let _ : LocallyOfFiniteType (cyclicHomSourceCurve n g).group.hom := by
    rw [← (cyclicHomSourceCurve n g).inclusion.w]
    infer_instance
  let _ : FormallyUnramified
      (GroupTorsionScheme.scheme (cyclicHomSourceCurve n g).group n).hom :=
    auxiliarySchemeTorsion_formallyUnramified (cyclicHomAuxiliaryPoint n g) n hn
  obtain ⟨c, V, _, hxV, hc⟩ := a.exists_local_curveMarking_relabel_of_torsion
    ((cyclicHomSubgroup n f hf).orbitGenerator_cartier (cyclicHomSourceMarking n f)
      (cyclicHomSubgroup_ideal n f hf))
    ((cyclicHomSubgroup n g hg).orbitGenerator_cartier (cyclicHomSourceMarking n g)
      (cyclicHomSubgroup_ideal n g hg)) x
  rw [orbitGenerator_curveMarking, orbitGenerator_curveMarking] at hc
  obtain ⟨W, hW, hxW, hWV⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  refine ⟨r, c, W, hW, hxW, ?_, ?_⟩
  · intro i
    have h := congrArg (T.homOfLE (hWV.trans inf_le_left) ≫ ·) (hr i)
    simpa only [← Category.assoc, Scheme.homOfLE_ι] using h
  · intro i
    have h := congrArg (T.homOfLE (hWV.trans inf_le_right) ≫ ·) (hc i)
    simpa only [← Category.assoc, Scheme.homOfLE_ι] using h

end FLT.Mazur.OddWeierstrassParameter
