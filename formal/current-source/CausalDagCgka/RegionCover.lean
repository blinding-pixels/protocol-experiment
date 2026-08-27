import Std

namespace CausalDagCgka

/-- Fixed-length bit paths naming leaves in a complete binary key tree. -/
inductive Bits : Nat → Type
  | nil : Bits 0
  | cons {d : Nat} : Bool → Bits d → Bits (d + 1)

/-- A dyadic subtree block inside a depth-`d` complete binary key tree. -/
inductive Block : Nat → Type
  | root (d : Nat) : Block d
  | left {d : Nat} : Block d → Block (d + 1)
  | right {d : Nat} : Block d → Block (d + 1)

namespace Block

/-- Whether a dyadic block contains a leaf. -/
def contains : {d : Nat} → Block d → Bits d → Prop
  | _, root _, _ => True
  | _, left b, Bits.cons bit rest => bit = false ∧ contains b rest
  | _, right b, Bits.cons bit rest => bit = true ∧ contains b rest

end Block

/--
A prefix region in a segment-local namespace. Every constructor denotes a
prefix of the leaves ordered with `false` before `true`.

Forks and membership changes start fresh segment namespaces. A retrospective
grant is therefore a bounded union of these segment prefixes, not an arbitrary
DAG subset.
-/
inductive PrefixRegion : Nat → Type
  | empty (d : Nat) : PrefixRegion d
  | full (d : Nat) : PrefixRegion d
  | left {d : Nat} : PrefixRegion d → PrefixRegion (d + 1)
  | overLeft {d : Nat} : PrefixRegion d → PrefixRegion (d + 1)

namespace PrefixRegion

/-- Semantic membership in a segment prefix. -/
def contains : {d : Nat} → PrefixRegion d → Bits d → Prop
  | _, empty _, _ => False
  | _, full _, _ => True
  | _, left p, Bits.cons bit rest => bit = false ∧ contains p rest
  | _, overLeft p, Bits.cons bit rest =>
      bit = false ∨ (bit = true ∧ contains p rest)

/-- Canonical dyadic subtree cover of a segment prefix. -/
def cover : {d : Nat} → PrefixRegion d → List (Block d)
  | _, empty _ => []
  | d, full _ => [Block.root d]
  | _, left p => (cover p).map Block.left
  | _, overLeft p =>
      Block.left (Block.root _) :: (cover p).map Block.right

private theorem leftMapExact {d : Nat} (blocks : List (Block d)) (x : Bits d) :
    (∃ b ∈ blocks.map Block.left,
      Block.contains b (Bits.cons false x)) ↔
    (∃ b ∈ blocks, Block.contains b x) := by
  constructor
  · rintro ⟨b, hb, hbx⟩
    rcases List.mem_map.mp hb with ⟨a, ha, hab⟩
    subst b
    exact ⟨a, ha, hbx.2⟩
  · rintro ⟨a, ha, hax⟩
    refine ⟨Block.left a, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨a, ha, rfl⟩
    · exact ⟨rfl, hax⟩

private theorem overLeftMapExact {d : Nat} (blocks : List (Block d)) (x : Bits d) :
    (∃ b ∈ Block.left (Block.root d) :: blocks.map Block.right,
      Block.contains b (Bits.cons true x)) ↔
    (∃ b ∈ blocks, Block.contains b x) := by
  constructor
  · rintro ⟨b, hb, hbx⟩
    rcases List.mem_cons.mp hb with hHead | hTail
    · subst b
      simp [Block.contains] at hbx
    · rcases List.mem_map.mp hTail with ⟨a, ha, hab⟩
      subst b
      exact ⟨a, ha, hbx.2⟩
  · rintro ⟨a, ha, hax⟩
    refine ⟨Block.right a, ?_, ?_⟩
    · exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))
    · exact ⟨rfl, hax⟩

/-- The cover grants exactly the intended prefix and nothing else. -/
theorem cover_exact {d : Nat} (p : PrefixRegion d) (x : Bits d) :
    contains p x ↔ ∃ b ∈ cover p, Block.contains b x := by
  induction p with
  | empty d =>
      simp [contains, cover]
  | full d =>
      simp [contains, cover, Block.contains]
  | left p ih =>
      cases x with
      | cons bit rest =>
          cases bit with
          | false =>
              simp only [contains, cover]
              rw [leftMapExact]
              simpa using ih rest
          | true =>
              simp [contains, cover, Block.contains]
  | overLeft p ih =>
      cases x with
      | cons bit rest =>
          cases bit with
          | false =>
              simp [contains, cover, Block.contains]
          | true =>
              simp only [contains, cover]
              rw [overLeftMapExact]
              simpa using ih rest

/-- A single segment-prefix capability needs at most `d + 1` subtree keys. -/
theorem cover_length_le_depth_plus_one {d : Nat} (p : PrefixRegion d) :
    (cover p).length ≤ d + 1 := by
  induction p with
  | empty d =>
      simp [cover]
  | full d =>
      simp [cover]
  | @left d p ih =>
      simp only [cover, List.length_map]
      exact Nat.le_trans ih (Nat.le_succ (d + 1))
  | @overLeft d p ih =>
      simp only [cover, List.length_cons, List.length_map]
      omega

/-- Cover a bounded union of segment prefixes. -/
def coverMany {d : Nat} : List (PrefixRegion d) → List (Block d)
  | [] => []
  | p :: ps => cover p ++ coverMany ps

/-- `b` segment prefixes need at most `b * (d + 1)` subtree keys. -/
theorem coverMany_length_le {d : Nat} (regions : List (PrefixRegion d)) :
    (coverMany regions).length ≤ regions.length * (d + 1) := by
  induction regions with
  | nil =>
      simp [coverMany]
  | cons p ps ih =>
      simp only [coverMany, List.length_append, List.length_cons]
      have hp := cover_length_le_depth_plus_one p
      calc
        (cover p).length + (coverMany ps).length
            ≤ (d + 1) + ps.length * (d + 1) := Nat.add_le_add hp ih
        _ = ps.length * (d + 1) + (d + 1) := Nat.add_comm _ _
        _ = (ps.length + 1) * (d + 1) := by
          rw [Nat.add_mul]
          simp

/-- The union cover is extensionally exact. -/
theorem coverMany_exact {d : Nat} (regions : List (PrefixRegion d)) (x : Bits d) :
    (∃ p ∈ regions, contains p x) ↔
      (∃ b ∈ coverMany regions, Block.contains b x) := by
  induction regions with
  | nil =>
      simp [coverMany]
  | cons p ps ih =>
      constructor
      · rintro ⟨region, hRegion, hx⟩
        rcases List.mem_cons.mp hRegion with hHead | hTail
        · subst region
          rcases (cover_exact p x).mp hx with ⟨b, hb, hbx⟩
          refine ⟨b, ?_, hbx⟩
          change b ∈ cover p ++ coverMany ps
          exact List.mem_append.mpr (Or.inl hb)
        · rcases ih.mp ⟨region, hTail, hx⟩ with ⟨b, hb, hbx⟩
          refine ⟨b, ?_, hbx⟩
          change b ∈ cover p ++ coverMany ps
          exact List.mem_append.mpr (Or.inr hb)
      · rintro ⟨b, hb, hbx⟩
        change b ∈ cover p ++ coverMany ps at hb
        rcases List.mem_append.mp hb with hHead | hTail
        · refine ⟨p, List.mem_cons.mpr (Or.inl rfl), ?_⟩
          exact (cover_exact p x).mpr ⟨b, hHead, hbx⟩
        · rcases ih.mpr ⟨b, hTail, hbx⟩ with ⟨region, hRegion, hx⟩
          exact ⟨region, List.mem_cons.mpr (Or.inr hRegion), hx⟩

end PrefixRegion

end CausalDagCgka
