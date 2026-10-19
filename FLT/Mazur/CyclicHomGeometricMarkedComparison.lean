/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryGeometricRelabel
public import FLT.Mazur.CompatibleGeometricGeneratorRelabel
public import FLT.Mazur.CyclicHomMultiplicationEquation
public import FLT.Mazur.OrbitGeneratorCurveMarking

/-!
# Geometric compatible comparisons align both independent source markings

The auxiliary and cyclic automorphisms are extracted from the same given full
comparison. All cyclic labels are retained even when they coincide.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {K : Type} [Field K] [IsAlgClosed K]
  (f g : Spec (.of K) ⟶ (cyclicHomAuxiliaryScheme n).left)
  (hf : cyclicHomMultiplicationEquation n f = 0)
  (hg : cyclicHomMultiplicationEquation n g = 0)
  (a : CompatibleIso (cyclicHomSubgroup n f hf) (cyclicHomSubgroup n g hg))

/-- A full original geometric comparison matches both entire source frames after relabeling. -/
theorem cyclicHom_geometric_marking_relabel :
    ∃ (r : MulAut (Labels 4)) (c : MulAut (Multiplicative (ZMod n))),
      (∀ i, auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) (r i) ≫
        a.curve.hom.group = auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n g) i) ∧
      (∀ i, cyclicHomSourceMarking n f (c i) ≫ a.curve.hom.group =
        cyclicHomSourceMarking n g i) := by
  let _ : IsMonHom (groupIso a.curve).hom :=
    inferInstanceAs (IsMonHom a.curve.hom.group)
  let e : auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n f) ≅
      auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n g) :=
    CommGrp.mkIso' (groupIso a.curve)
  obtain ⟨r, hr, _⟩ := auxiliarySchemeMarking_geometric_relabel _ _ e
  obtain ⟨c, hc⟩ := a.exists_geometric_curveMarking_relabel
    ((cyclicHomSubgroup n f hf).orbitGenerator_cartier (cyclicHomSourceMarking n f)
      (cyclicHomSubgroup_ideal n f hf))
    ((cyclicHomSubgroup n g hg).orbitGenerator_cartier (cyclicHomSourceMarking n g)
      (cyclicHomSubgroup_ideal n g hg))
  rw [orbitGenerator_curveMarking, orbitGenerator_curveMarking] at hc
  exact ⟨r, c, hr, hc⟩

end FLT.Mazur.UniversalWeierstrass
