/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupBaseChangeCompEq
public import FLT.Mazur.CompatibleSubgroupIsoFaithful

/-!
# Coherence of the actual finite subgroup pullback comparisons

Naturality and the threefold comparison identity hold for the full compatible
subgroup data. Faithfulness reduces each identity to its established DR square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}

/-- Direct-to-iterated comparison commutes with every compatible subgroup isomorphism. -/
theorem CompatibleIso.baseChange_comp_natural (a : CompatibleIso H J)
    (g : T ⟶ S) (h : U ⟶ T) :
    (compatibleBaseChangeComp H g h).trans ((a.baseChange g).baseChange h) =
      (a.baseChange (h ≫ g)).trans (compatibleBaseChangeComp J g h) := by
  apply CompatibleIso.ext_curve_hom
  exact ((GeneralizedEllipticCurve.baseChangeComp g h).hom.naturality a.curve.hom).symm

/-- The actual subgroup comparisons satisfy the same threefold coherence as the full curves. -/
theorem compatibleBaseChangeComp_assoc (H : E.FiniteSubgroup n)
    (g : T ⟶ S) (h : U ⟶ T) (k : V ⟶ U) :
    (compatibleBaseChangeComp H g (k ≫ h)).trans
      (compatibleBaseChangeComp (H.baseChange g) h k) =
    (compatibleBaseChangeCompEq H (h ≫ g) k ((k ≫ h) ≫ g) (Category.assoc k h g)).trans
      ((compatibleBaseChangeComp H g h).baseChange k) := by
  apply CompatibleIso.ext_curve_hom
  change (E.baseChangeCompIso g (k ≫ h)).hom ≫
    ((E.baseChange g).baseChangeCompIso h k).hom =
      (compatibleBaseChangeCompEq H (h ≫ g) k _ _).curve.hom ≫
        (baseChangeFunctor k).map (E.baseChangeCompIso g h).hom
  rw [compatibleBaseChangeCompEq_curve]
  simpa only [baseChangeCompEqIso, Iso.trans_hom, Category.assoc, Iso.app_hom,
    baseChangeFunctor] using
    E.baseChange_assoc g h k

/-- Extending a compatible fiber comparison twice agrees with extending along the composite. -/
theorem compatibleBaseChangeExtension_comp (H : E.FiniteSubgroup n)
    (g : T ⟶ S) {D : GeneralizedEllipticCurve T} {A : D.FiniteSubgroup n}
    (a : CompatibleIso (H.baseChange g) A) (h : U ⟶ T) (k : V ⟶ U) :
    ((compatibleBaseChangeComp H g (k ≫ h)).trans (a.baseChange (k ≫ h))).trans
      (compatibleBaseChangeComp A h k) =
    (compatibleBaseChangeCompEq H (h ≫ g) k ((k ≫ h) ≫ g) (Category.assoc k h g)).trans
      (((compatibleBaseChangeComp H g h).trans (a.baseChange h)).baseChange k) := by
  rw [CompatibleIso.trans_assoc, ← CompatibleIso.baseChange_comp_natural a h k,
    ← CompatibleIso.trans_assoc, compatibleBaseChangeComp_assoc,
    CompatibleIso.trans_assoc, ← CompatibleIso.baseChange_trans]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
