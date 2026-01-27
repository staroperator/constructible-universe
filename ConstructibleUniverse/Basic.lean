import Mathlib.ModelTheory.Definability
import Mathlib.SetTheory.ZFC.VonNeumann
import ConstructibleUniverse.Language
import ConstructibleUniverse.ZFSet

universe u v

open FirstOrder Language in
theorem Set.univ_definable_iff {M : Type*} {L : FirstOrder.Language.{u, v}} [L.Structure M]
    {α : Type*} {s : Set (α → M)} :
    Set.univ.Definable L s ↔ ∃ φ : L.Formula (M ⊕ α), s = {v | φ.Realize (Sum.elim id v)} := by
  rw [definable_iff_exists_formula_sum,
    Equiv.exists_congr_left (BoundedFormula.relabelEquiv <| .sumCongr (Equiv.Set.univ M) (.refl α))]
  refine exists_congr (fun φ => iff_iff_eq.2 (congr_arg (s = ·) ?_))
  ext
  simp only [Formula.Realize, BoundedFormula.relabelEquiv,
    BoundedFormula.mapTermRelEquiv_symm_apply, Equiv.refl_symm, Equiv.coe_refl, mem_setOf_eq]
  refine BoundedFormula.realize_mapTermRel_id ?_ (fun _ _ _ => rfl)
  intros
  simp only [Term.relabelEquiv_symm_apply, Equiv.sumCongr_symm, Equiv.refl_symm,
    Term.realize_relabel]
  congr 1 with a
  rcases a with (_ | _) | _ <;> rfl

namespace ZFSet

lemma sep_subset_self (x : ZFSet) (p) : ZFSet.sep p x ⊆ x := by
  intro _ h
  exact (mem_sep.1 h).1

open FirstOrder Language

def «def» (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => (Set.univ : Set x).Definable₁ set { z : x | z.1 ∈ y }) (powerset x)

variable {x y a b : ZFSet}

theorem def_subset_powerset : a.def ⊆ a.powerset :=
  sep_subset_self _ _

theorem subset_of_mem_def : x ∈ a.def → x ⊆ a :=
  (mem_powerset.1 <| def_subset_powerset ·)

theorem mem_def_iff :
    x ∈ a.def ↔ x ⊆ a ∧ ∃ φ : set.Formula (a ⊕ Fin 1),
      ∀ y, y.1 ∈ x ↔ φ.Realize (Sum.elim id ![y]) := by
  rw [ZFSet.def, mem_sep, mem_powerset, Set.Definable₁, Set.univ_definable_iff]
  congr!
  simp_rw [Set.ext_iff, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  rfl

theorem mem_def_self : a ∈ a.def := by
  rw [mem_def_iff]
  refine ⟨subset_rfl, ⊤, fun y => ?_⟩
  simp

theorem empty_mem_def : ∅ ∈ a.def := by
  rw [mem_def_iff]
  refine ⟨empty_subset _, ⊥, fun y => ?_⟩
  simp

theorem union_mem_def : x ∈ a.def → y ∈ a.def → x ∪ y ∈ a.def := by
  simp only [mem_def_iff]
  intro ⟨hx, φ, hφ⟩ ⟨hy, ψ, hψ⟩
  refine ⟨union_subset hx hy, φ ⊔ ψ, fun z => ?_⟩
  simp [← hφ, hψ]

theorem intersect_mem_def : x ∈ a.def → y ∈ a.def → x ∩ y ∈ a.def := by
  simp only [mem_def_iff]
  intro ⟨hx, φ, hφ⟩ ⟨hy, ψ, hψ⟩
  refine ⟨inter_subset_left.trans hx, φ ⊓ ψ, fun z => ?_⟩
  simp [← hφ, hψ]

theorem sdiff_mem_def : x ∈ a.def → a \ x ∈ a.def := by
  simp only [mem_def_iff]
  intro ⟨hy, φ, hφ⟩
  refine ⟨sdiff_subset, ∼ φ, fun z => ?_⟩
  simp [← hφ]

-- theorem def_trans : x ∈ a.def → a ∈ b.def → x ∈ b.def := by
--   sorry

theorem isTransitive_def (ha : a.IsTransitive) : a.def.IsTransitive := by
  intro x hx y hy
  apply subset_of_mem_def at hx
  apply hx at hy
  rw [mem_def_iff]
  refine ⟨ha _ hy, &0 ∈' &'⟨y, hy⟩, fun z => ?_⟩
  simp

theorem subset_def_self (ha : a.IsTransitive) : a ⊆ a.def := by
  apply isTransitive_def ha
  exact mem_def_self

noncomputable def constructible (o : Ordinal.{u}) : ZFSet.{u} :=
  ⋃ a : Set.Iio o, (constructible a).def
termination_by o
decreasing_by exact a.2

scoped notation "L_ " => constructible

open Order

variable {o a b : Ordinal}

theorem constructible_zero : L_ 0 = ∅ := by
  rw [constructible]
  ext
  simp

theorem constructible_mono (h : a ≤ b) : L_ a ⊆ L_ b := by
  rw [constructible, constructible]
  intro x
  simp only [mem_iUnion]
  exact fun ⟨o, hx⟩ => ⟨⟨o.1, o.2.trans_le h⟩, hx⟩

theorem isTransitive_constructible : (L_ o).IsTransitive := by
  induction o using Ordinal.induction with | _ o ih
  rw [constructible]
  exact IsTransitive.iUnion fun ⟨k, hk⟩ => isTransitive_def (ih k hk)

theorem constructible_succ : L_ (Order.succ o) = (L_ o).def := by
  conv_lhs => rw [constructible]
  ext x
  simp only [mem_iUnion, Subtype.exists, Set.mem_Iio, exists_prop, Order.lt_succ_iff]
  refine ⟨fun ⟨a, ha, hx⟩ => ?_, fun hx => ⟨o, le_rfl, hx⟩⟩
  rcases ha.eq_or_lt with rfl | ha
  · exact hx
  · apply subset_def_self isTransitive_constructible
    rw [constructible]
    exact mem_iUnion.2 ⟨⟨a, ha⟩, hx⟩

theorem constructible_of_isSuccPrelimit (ho : IsSuccPrelimit o) :
    L_ o = ⋃ a : Set.Iio o, L_ a.1 := by
  conv_lhs => rw [constructible]
  ext x
  simp only [mem_iUnion, Subtype.exists, Set.mem_Iio, exists_prop]
  exact ⟨fun ⟨a, ha, hx⟩ => ⟨succ a, ho.succ_lt ha, by rwa [constructible_succ]⟩,
    fun ⟨a, ha, hx⟩ => ⟨a, ha, subset_def_self isTransitive_constructible hx⟩⟩

theorem constructible_subset_vonNeumann : L_ o ⊆ V_ o := by
  induction o using Ordinal.induction with | _ o ih
  rw [constructible, vonNeumann]
  exact iUnion_subset_iUnion fun ⟨a, ha⟩ =>
    def_subset_powerset.trans <| powerset_mono <| ih a ha

end ZFSet
