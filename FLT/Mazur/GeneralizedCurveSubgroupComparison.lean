/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGeneratorTransport

/-!
# Generators and canonical subgroup pullback comparisons

The actual subgroup comparisons preserve the curve embedding and group law,
so existence of a Cartier generator is independent of pullback parenthesization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S T U : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n)

/-- The identity subgroup comparison preserves existence of generators. -/
theorem exists_generator_id_iff :
    (∃ P, (H.baseChange (𝟙 S)).IsCartierGenerator P) ↔ ∃ P, H.IsCartierGenerator P := by
  let d : (H.baseChange (𝟙 S)).carrier ≅ H.carrier := Over.pullbackId.app H.carrier
  let : IsMonHom d.hom :=
    inferInstanceAs (IsMonHom ((Functor.mapMonNatIso Over.pullbackId).hom.app
      (Mon.mk H.carrier)).hom)
  apply exists_generator_iff _ _ E.baseChangeIdIso d
  simpa only [baseChange_curveMap, baseChangeIdIso, isoMk, pullbackCurveIdIso,
    d, Iso.app_hom, Functor.id_map] using Over.pullbackId.hom.naturality H.curveMap

/-- Direct and iterated subgroup pullback have Cartier generators simultaneously. -/
theorem exists_generator_comp_iff (g : T ⟶ S) (h : U ⟶ T) :
    (∃ P, (H.baseChange (h ≫ g)).IsCartierGenerator P) ↔
      ∃ P, ((H.baseChange g).baseChange h).IsCartierGenerator P := by
  let d : (H.baseChange (h ≫ g)).carrier ≅ ((H.baseChange g).baseChange h).carrier :=
    (Over.pullbackComp h g).app H.carrier
  let : IsMonHom d.hom :=
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
  apply exists_generator_iff _ _ (E.baseChangeCompIso g h) d
  simpa only [baseChange_curveMap, baseChangeCompIso, isoMk, pullbackCurveCompIso,
    d, Iso.app_hom, Functor.comp_map] using
    (Over.pullbackComp h g).hom.naturality H.curveMap

/-- Equal base maps give the same generator-existence predicate. -/
theorem exists_generator_congr {g h : T ⟶ S} (e : g = h) :
    (∃ P, (H.baseChange g).IsCartierGenerator P) ↔
      ∃ P, (H.baseChange h).IsCartierGenerator P := by subst h; rfl

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
