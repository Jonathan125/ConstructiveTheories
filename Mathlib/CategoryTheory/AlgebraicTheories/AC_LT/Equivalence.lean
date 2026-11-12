/-
Copyright (c) 2026 Jonathan Konig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Konig
-/
import Mathlib.CategoryTheory.AlgebraicTheories.AC_LT.Unit
import Mathlib.CategoryTheory.AlgebraicTheories.AC_LT.Counit

/-!
# Equivalence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


namespace CategoryTheory

namespace AlgebraicTheories

namespace AC_LT

universe u

protected theorem unitIso_comp (A : AbstractClone.{u}) :
    ACtoLT.func.map (AC_LT.unit.hom.app A) ≫ AC_LT.counit.hom.app (ACtoLT.func.obj A)
    = 𝟙 (ACtoLT.func.obj A) :=
  LawvereTheory.Hom.ext <| Functor.ext (LawvereTheory.Hom.comp_obj _ _) <|
  fun _ _ _ ↦ LTtoAC.coproduct_iso_inv_inj _ _ _ <| (LTtoAC.coproduct_iso_hom_inv_id _ _).trans <|
  funext <| fun _ ↦ funext <| fun _ ↦ Eq.symm <| (A.projection _ _).trans <|
  (A.projection _ _).trans <| A.identity _


protected def equivalence : AbstractClone.{u} ≌ LawvereTheory.{u, u, u} where
  functor := ACtoLT.func
  inverse := LTtoAC.func
  unitIso := AC_LT.unit
  counitIso := AC_LT.counit
  functor_unitIso_comp := AC_LT.unitIso_comp

end AC_LT

end AlgebraicTheories

end CategoryTheory
