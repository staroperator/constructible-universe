import Mathlib.ModelTheory.Substructures
import Mathlib.SetTheory.ZFC.Basic

namespace FirstOrder.Language

scoped[FirstOrder] prefix:arg "&'" => FirstOrder.Language.Term.var ∘ Sum.inl

inductive setRel : ℕ → Type where
  | mem : setRel 2

def set : Language where
  Functions _ := Empty
  Relations := setRel

abbrev set.memRel : set.Relations 2 := setRel.mem

def BoundedFormula.mem {α n} (t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  set.memRel.boundedFormula₂ t₁ t₂

def Formula.mem {α} (t₁ t₂ : set.Term α) : set.Formula α :=
  set.memRel.formula₂ t₁ t₂

scoped[FirstOrder] infix:60 " ∈' " => Language.Formula.mem

end FirstOrder.Language

namespace ZFSet

open FirstOrder Language

instance : set.Structure ZFSet where
  funMap := nofun
  RelMap
  | .mem, v => v 0 ∈ v 1

@[simp]
theorem relMap_mem {v} : Structure.RelMap (M := ZFSet) set.memRel v ↔ v 0 ∈ v 1 :=
  Iff.rfl

@[simp]
theorem realize_mem {α} {t₁ t₂ : set.Term α} {v} :
    Formula.Realize (M := ZFSet) (t₁ ∈' t₂) v ↔ Term.realize v t₁ ∈ Term.realize v t₂ := by
  simp [Formula.mem]

def toSubstructure (x : ZFSet) : Substructure set ZFSet where
  carrier := x
  fun_mem := nofun

variable {x : ZFSet}

instance : set.Structure x := inferInstanceAs (set.Structure x.toSubstructure)

@[simp]
theorem relMap_mem' {v} : Structure.RelMap (M := x) set.memRel v ↔ (v 0).1 ∈ (v 1).1 :=
  Iff.rfl

@[simp]
theorem realize_mem' {α} {t₁ t₂ : set.Term α} {v} :
    Formula.Realize (M := x) (t₁ ∈' t₂) v ↔ (Term.realize v t₁).1 ∈ (Term.realize v t₂).1 := by
  simp [Formula.mem]

end ZFSet
