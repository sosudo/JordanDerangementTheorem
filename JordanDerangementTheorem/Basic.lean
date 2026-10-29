import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib
import Architect

namespace JordanDerangementTheorem

open MulAction

/-- Jordan's derangement theorem: a finite transitive permutation group on a nontrivial set contains
a derangement (equivalently, a fixed-point-free element). The Burnside fixed-point sum
contradicts every element having a fixed point, since the identity fixes more than one. -/
@[blueprint "JordanDerangementTheorem.MainTheorem"]
theorem MainTheorem {α : Type*} [Finite α] [Nontrivial α]
    {G : Subgroup (Equiv.Perm α)} (hG : IsPretransitive G α) :
    ∃ g : Equiv.Perm α, g ∈ G ∧ g ∈ derangements α := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite G
  letI : IsPretransitive G α := hG
  letI : Fintype (orbitRel.Quotient G α) := Fintype.ofFinite _
  have hc : Fintype.card (orbitRel.Quotient G α) = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    obtain ⟨a⟩ := (inferInstance : Nonempty α)
    refine ⟨Quotient.mk'' a, ?_⟩
    intro q
    induction q using Quotient.inductionOn with
    | _ b =>
      apply Quotient.sound
      change (orbitRel G α) b a
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr (exists_smul_eq G a b))
  have hb := sum_card_fixedBy_eq_card_orbits_mul_card_group G α
  rw [hc, one_mul] at hb
  by_contra h
  have hp (g : G) : 1 ≤ Fintype.card (fixedBy α g) := by
    have hnempty : Nonempty (fixedBy α g) := by
     by_contra hn
     apply h
     refine ⟨g, g.property, ?_⟩
     intro x hx
     apply hn
     exact ⟨⟨x, hx⟩⟩
    exact Fintype.card_pos_iff.mpr hnempty
  have hi : 1 < Fintype.card (fixedBy α (1 : G)) := by
    have he : fixedBy α (1 : G) = Set.univ := by ext x; simp [fixedBy]
    have hcard : Fintype.card (fixedBy α (1 : G)) = Fintype.card α :=
      Fintype.card_congr ((Equiv.Set.univ α |>.symm.trans (Equiv.setCongr he.symm)).symm)
    rw [hcard]
    exact Fintype.one_lt_card
  have hs : (∑ _g : G, (1 : ℕ)) < ∑ g : G, Fintype.card (fixedBy α g) := by
    apply Finset.sum_lt_sum
    · intro g hg; exact hp g
    · exact ⟨1, Finset.mem_univ _, hi⟩
  have hs' : Fintype.card G < ∑ g : G, Fintype.card (fixedBy α g) := by simpa using hs
  omega

end JordanDerangementTheorem
