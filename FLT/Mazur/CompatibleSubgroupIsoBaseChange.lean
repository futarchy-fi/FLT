/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Base change of compatible subgroup isomorphisms

Pullback acts on both geometric isomorphisms and preserves the inclusion
square. The canonical identity and composition comparisons are compatible
isomorphisms of the actual finite subgroup data.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

variable {S T U : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}

/-- Arbitrary base change preserves compatible subgroup isomorphisms. -/
def CompatibleIso.baseChange (a : CompatibleIso H J) (g : T ⟶ S) :
    CompatibleIso (H.baseChange g) (J.baseChange g) where
  curve := (baseChangeFunctor g).mapIso a.curve
  subgroup := (Over.pullback g).mapIso a.subgroup
  isMonHom := inferInstanceAs (IsMonHom ((Over.pullback g).map a.subgroup.hom))
  compatible := by
    simp only [baseChange_curveMap]
    change (Over.pullback g).map H.curveMap ≫ (Over.pullback g).map a.curve.hom.curve =
      (Over.pullback g).map a.subgroup.hom ≫ (Over.pullback g).map J.curveMap
    rw [← Functor.map_comp, a.compatible, Functor.map_comp]

/-- Pullback preserves identity compatible isomorphisms. -/
theorem CompatibleIso.baseChange_refl (H : E.FiniteSubgroup n) (g : T ⟶ S) :
    (CompatibleIso.refl H).baseChange g = CompatibleIso.refl (H.baseChange g) := by
  apply CompatibleIso.ext <;>
    simp only [CompatibleIso.baseChange, CompatibleIso.refl, Functor.mapIso_refl] <;> rfl

/-- Pullback preserves composition of compatible isomorphisms. -/
theorem CompatibleIso.baseChange_trans {G : GeneralizedEllipticCurve S}
    {A : G.FiniteSubgroup n} (a : CompatibleIso H J) (b : CompatibleIso J A) (g : T ⟶ S) :
    (a.trans b).baseChange g = (a.baseChange g).trans (b.baseChange g) := by
  apply CompatibleIso.ext <;> simp [CompatibleIso.baseChange, CompatibleIso.trans]

/-- The canonical identity pullback comparison respects the actual subgroup inclusion. -/
def compatibleBaseChangeId (H : E.FiniteSubgroup n) :
    CompatibleIso (H.baseChange (𝟙 S)) H := by
  let d : (H.baseChange (𝟙 S)).carrier ≅ H.carrier := Over.pullbackId.app H.carrier
  let _ : IsMonHom d.hom :=
    inferInstanceAs (IsMonHom ((Functor.mapMonNatIso Over.pullbackId).hom.app
      (Mon.mk H.carrier)).hom)
  refine ⟨E.baseChangeIdIso, d, ?_⟩
  simpa only [baseChange_curveMap, baseChangeIdIso, isoMk, pullbackCurveIdIso,
    d, Iso.app_hom, Functor.id_map] using Over.pullbackId.hom.naturality H.curveMap

/-- The direct and iterated subgroup pullbacks are compatibly isomorphic. -/
def compatibleBaseChangeComp (H : E.FiniteSubgroup n) (g : T ⟶ S) (h : U ⟶ T) :
    CompatibleIso (H.baseChange (h ≫ g)) ((H.baseChange g).baseChange h) := by
  let d : (H.baseChange (h ≫ g)).carrier ≅ ((H.baseChange g).baseChange h).carrier :=
    (Over.pullbackComp h g).app H.carrier
  let _ : IsMonHom d.hom :=
    { one_hom := by
        change η[(Over.pullback (h ≫ g)).obj H.carrier] ≫ d.hom =
          η[(Over.pullback h).obj ((Over.pullback g).obj H.carrier)]
        simpa only [Functor.obj.η_def, d, Iso.app_hom,
          Functor.comp_obj, Functor.comp_map, Functor.LaxMonoidal.comp_ε,
          Functor.map_comp, Category.assoc]
          using MonoidalActionMap.unit_naturality (η[H.carrier]) (Over.pullbackComp h g).hom
      mul_hom := by
        change μ[(Over.pullback (h ≫ g)).obj H.carrier] ≫ d.hom =
          (d.hom ⊗ₘ d.hom) ≫ μ[(Over.pullback h).obj ((Over.pullback g).obj H.carrier)]
        simpa only [Functor.obj.μ_def, d, Iso.app_hom,
          Functor.comp_obj, Functor.comp_map, Functor.LaxMonoidal.comp_μ,
          Functor.map_comp, Category.assoc]
          using MonoidalActionMap.naturality (μ[H.carrier]) (Over.pullbackComp h g).hom }
  refine ⟨E.baseChangeCompIso g h, d, ?_⟩
  simpa only [baseChange_curveMap, baseChangeCompIso, isoMk, pullbackCurveCompIso,
    d, Iso.app_hom, Functor.comp_map] using (Over.pullbackComp h g).hom.naturality H.curveMap

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
