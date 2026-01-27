import Mathlib.SetTheory.ZFC.Basic

namespace ZFSet

universe u

variable {x y z : ZFSet.{u}}

theorem union_subset : x ⊆ z → y ⊆ z → x ∪ y ⊆ z := by
  grind [subset_def, mem_union]

theorem inter_subset_left : x ∩ y ⊆ x := by
  grind [subset_def, mem_inter]

theorem inter_subset_right : x ∩ y ⊆ y := by
  grind [subset_def, mem_inter]

theorem sdiff_subset : x \ y ⊆ x := by
  grind [subset_def, mem_sdiff]

theorem powerset_subset_powerset : powerset x ⊆ powerset y ↔ x ⊆ y := by
  simp_rw [subset_def, mem_powerset]
  exact ⟨fun h z hz => h subset_rfl hz, fun h z hz a ha => h (hz ha)⟩

alias ⟨_, powerset_mono⟩ := powerset_subset_powerset

theorem iUnion_subset_iUnion {α} [Small.{u} α] {f g : α → ZFSet.{u}}
    (h : ∀ i, f i ⊆ g i) : ⋃ i, f i ⊆ ⋃ i, g i := by
  simp only [subset_def, mem_iUnion]
  grind [subset_def]

end ZFSet
