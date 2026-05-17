import ForMathlib.ModelTheory.Definability
import Mathlib.Tactic.FinCases

namespace FirstOrder.Language

inductive setRel : ℕ → Type where
  | mem : setRel 2

def set : Language where
  Functions _ := Empty
  Relations := setRel

abbrev set.memRel : set.Relations 2 := setRel.mem

variable {α : Type*} {n : ℕ}

open set

def Term.mem (t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  set.memRel.boundedFormula₂ t₁ t₂

scoped[FirstOrder.Language.set] infix:88 " ∈' " => Term.mem

def Term.subset (t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  .all (&(Fin.last n) ∈' t₁.relabel (Sum.map id Fin.castSucc)
    ⟹ &(Fin.last n) ∈' t₂.relabel (Sum.map id Fin.castSucc))

scoped[FirstOrder.Language.set] infix:88 " ⊆' " => Term.subset

variable {M : Type*} [set.Structure M] {A : Set M} {a b c x y z : M}

namespace set

scoped instance : Membership M M where
  mem x y := Structure.RelMap set.memRel ![y, x]

@[simp]
theorem relMap_mem {v : Fin 2 → M} : Structure.RelMap set.memRel v ↔ v 0 ∈ v 1 := by
  simp only [Membership.mem]
  congr!
  funext x
  fin_cases x <;> simp

@[simp]
theorem realize_mem {t₁ t₂ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (t₁ ∈' t₂).Realize v w ↔ t₁.realize (Sum.elim v w) ∈ t₂.realize (Sum.elim v w) := by
  simp [Term.mem]


@[fun_prop]
theorem _root_.Set.DefinablePred.mem {f g : (α → M) → M} (hf : A.DefinableFun set f)
    (hg : A.DefinableFun set g) : A.DefinablePred set fun v => f v ∈ g v :=
  Set.DefinablePred.comp (A := A) (f := fun v => ![f v, g v]) (by simp [*]) (.rel set.memRel)

scoped instance : HasSubset M where
  Subset x y := ∀ ⦃z⦄, z ∈ x → z ∈ y

@[grind =]
theorem subset_def : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y := Iff.rfl

instance : Std.Refl (· ⊆ · : M → M → Prop) where
  refl := by grind

instance : IsTrans M (· ⊆ ·) where
  trans := by grind

scoped instance : HasSSubset M where
  SSubset x y := x ⊆ y ∧ x ≠ y

@[grind =]
theorem ssubset_def : x ⊂ y ↔ x ⊆ y ∧ x ≠ y := Iff.rfl

@[simp]
theorem realize_subset {t₁ t₂ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (t₁ ⊆' t₂).Realize v w ↔ Term.realize (Sum.elim v w) t₁ ⊆ Term.realize (Sum.elim v w) t₂ := by
  simp [Term.subset, subset_def, Sum.elim_comp_map]

@[fun_prop]
theorem _root_.Set.DefinablePred.subset [Finite α] {f g : (α → M) → M} (hf : A.DefinableFun set f)
    (hg : A.DefinableFun set g) : A.DefinablePred set fun v => f v ⊆ g v := by
  simp_rw [subset_def]
  fun_prop

scoped instance (priority := 100) : CoeSort M (Type _) :=
  ⟨fun p => { x : M // x ∈ p }⟩

open Lean PrettyPrinter.Delaborator SubExpr in
@[app_delab Subtype]
meta def delabSubtype : Delab := whenPPOption getPPNotation do
  let #[_, .lam n _ body _] := (← getExpr).getAppArgs | failure
  guard <| body.isAppOf ``Membership.mem
  let #[_, _, inst, _, .bvar 0] := body.getAppArgs | failure
  guard <| inst.isAppOfArity ``set.instMembership 2
  let S ← withAppArg <| withBindingBody n <| withNaryArg 3 delab
  `(↥$S)

@[grind]
def Nonempty (x : M) :=
  ∃ y, y ∈ x

theorem nonempty_coe_sort : _root_.Nonempty ↥x ↔ Nonempty x :=
  nonempty_subtype

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort

@[fun_prop]
theorem _root_.Set.DefinablePred.nonempty [Finite α] {f : (α → M) → M}
    (hf : A.DefinableFun set f) : A.DefinablePred set fun v => Nonempty (f v) := by
  simp only [Nonempty]
  fun_prop

@[fun_prop]
def DefinablePred (p : ↥a → Prop) : Prop :=
  Set.univ.DefinablePred set fun v : Unit → M =>
    ∃ (h : v () ∈ a), p ⟨v (), h⟩

@[fun_prop]
def DefinableFun (f : ↥a → ↥b) : Prop :=
  Set.univ.DefinablePred set fun v : Fin 2 → M =>
    ∃ (h : v 0 ∈ a), (f ⟨v 0, h⟩).1 = v 1

@[fun_prop]
theorem DefinablePred.const (p : Prop) : DefinablePred fun _ : ↥a => p := by
  simp only [DefinablePred, exists_prop]
  fun_prop

@[fun_prop]
theorem DefinablePred.not {p : ↥a → Prop} (hp : DefinablePred p) :
    DefinablePred fun v => ¬ p v := by
  simp only [DefinablePred] at *
  convert hp.not.and (by fun_prop : Set.univ.DefinablePred set fun v : Unit → M => v () ∈ a)
  grind

@[fun_prop]
theorem DefinablePred.and {p q : ↥a → Prop} (hp : DefinablePred p) (hq : DefinablePred q) :
    DefinablePred fun v => p v ∧ q v := by
  simp only [DefinablePred] at *
  convert hp.and hq
  grind

@[fun_prop]
theorem DefinablePred.or {p q : ↥a → Prop} (hp : DefinablePred p) (hq : DefinablePred q) :
    DefinablePred fun v => p v ∨ q v := by
  simp only [DefinablePred] at *
  convert hp.or hq
  grind

@[fun_prop]
theorem DefinablePred.imp {p q : ↥a → Prop} (hp : DefinablePred p) (hq : DefinablePred q) :
    DefinablePred fun v => p v → q v := by
  simp_rw [imp_iff_not_or]
  fun_prop

@[fun_prop]
theorem DefinablePred.iff {p q : ↥a → Prop} (hp : DefinablePred p) (hq : DefinablePred q) :
    DefinablePred fun v => p v ↔ q v := by
  simp_rw [iff_iff_implies_and_implies]
  fun_prop

@[fun_prop]
theorem DefinablePred.comp {p : ↥b → Prop} {f : ↥a → ↥b} (hp : DefinablePred p)
    (hf : DefinableFun f) : DefinablePred fun x => p (f x) := by
  simp only [DefinablePred, DefinableFun] at *
  convert_to Set.univ.DefinablePred set fun v : Unit → M => ∃ (y : M),
    (∃ (h : v () ∈ a), (f ⟨v (), h⟩).1 = y) ∧ ∃ (h : y ∈ b), p ⟨y, h⟩
  · grind
  · refine .exists (.and ?_ ?_)
    · convert hf.comp (f := fun v => ![v (some ()), v none]) ?_
      intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;> fun_prop
    · convert hp.comp (f := fun v _ => v none) ?_
      fun_prop

@[fun_prop]
theorem DefinablePred.eq {f g : ↥a → ↥b} (hf : DefinableFun f) (hg : DefinableFun g) :
    DefinablePred fun x => f x = g x := by
  simp only [DefinableFun, DefinablePred] at *
  convert_to Set.univ.DefinablePred set fun v : Unit → M => ∃ (y : M) (z : M),
    (∃ (h : v () ∈ a), (f ⟨v (), h⟩).1 = y) ∧ (∃ (h : v () ∈ a), (g ⟨v (), h⟩).1 = y) ∧ y = z
  · grind
  · refine .exists (.exists (.and ?_ (.and ?_ (by fun_prop))))
    · convert hf.comp (f := fun v => ![v (some (some ())), v (some none)]) ?_
      intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;> fun_prop
    · convert hg.comp (f := fun v => ![v (some (some ())), v (some none)]) ?_
      intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;> fun_prop

@[fun_prop]
theorem DefinableFun.id : DefinableFun fun x : ↥a => x := by
  simp only [DefinableFun, exists_prop]
  fun_prop

@[fun_prop]
theorem DefinableFun.const (c : ↥b) : DefinableFun fun _ : ↥a => c := by
  simp only [DefinableFun, exists_prop]
  fun_prop

@[fun_prop]
theorem DefinableFun.comp {f : ↥a → ↥b} {g : ↥b → ↥c} (hf : DefinableFun f)
    (hg : DefinableFun g) : DefinableFun fun x => g (f x) := by
  simp only [DefinableFun] at *
  convert_to Set.univ.DefinablePred set fun v : Fin 2 → M => ∃ (y : M),
    (∃ (h : v 0 ∈ a), (f ⟨v 0, h⟩).1 = y) ∧ ∃ (h : y ∈ b), (g ⟨y, h⟩).1 = v 1
  · grind
  · refine .exists (.and ?_ ?_) <;> simp only [Function.comp_apply]
    · convert hf.comp (f := fun v : Option (Fin 2) → M => ![v (some 0), v none]) ?_
      intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;> fun_prop
    · convert hg.comp (f := fun v : Option (Fin 2) → M => ![v none, v (some 1)]) ?_
      intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;> fun_prop

@[fun_prop]
theorem DefinableFun.ite {f g : ↥a → ↥b} {p : ↥a → Prop} [DecidablePred p]
    (hf : DefinableFun f) (hg : DefinableFun g) (hp : DefinablePred p) :
    DefinableFun fun x => if p x then f x else g x := by
  simp only [DefinableFun, DefinablePred] at *
  replace hp' := hp.comp (f := fun (v : Fin 2 → M) _ => v 0) (by fun_prop)
  convert (hp'.and hf).or (hp'.not.and hg)
  grind

end FirstOrder.Language.set
